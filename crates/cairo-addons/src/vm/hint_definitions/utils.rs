use lazy_static::lazy_static;
use std::collections::HashMap;

use cairo_vm::{
    hint_processor::{
        builtin_hint_processor::hint_utils::{
            get_integer_from_var_name, get_maybe_relocatable_from_var_name, get_ptr_from_var_name,
            insert_value_from_var_name,
        },
        hint_processor_definition::HintReference,
    },
    serde::deserialize_program::ApTracking,
    types::{
        errors::math_errors::MathError, exec_scope::ExecutionScopes, relocatable::MaybeRelocatable,
    },
    vm::{errors::hint_errors::HintError, vm_core::VirtualMachine},
    Felt252,
};

use crate::vm::hints::Hint;
use revm_precompile::{
    blake2, bn128, hash, identity, kzg_point_evaluation, modexp, secp256k1, Address,
};

pub const HINTS: &[fn() -> Hint] = &[
    bytes__eq__,
    b_le_a,
    fp_plus_2_or_0,
    nibble_remainder,
    print_maybe_relocatable,
    precompile_index_from_address,
];

lazy_static! {
    static ref PRECOMPILE_INDICES: HashMap<Address, Felt252> = {
        let mut map = HashMap::new();
        // Using the imported precompiles, multiply index by 3 as per previous logic
        map.insert(secp256k1::ECRECOVER.0, Felt252::from(0));     // index 0
        map.insert(hash::SHA256.0, Felt252::from(3));             // index 1
        map.insert(hash::RIPEMD160.0, Felt252::from(2 * 3));          // index 2
        map.insert(identity::FUN.0, Felt252::from(3 * 3));       // index 3
        map.insert(modexp::BYZANTIUM.0, Felt252::from(4 * 3));          // index 4
        map.insert(bn128::add::BYZANTIUM.0, Felt252::from(5 * 3));              // index 5
        map.insert(bn128::mul::BYZANTIUM.0, Felt252::from(6 * 3));              // index 6
        map.insert(bn128::pair::ADDRESS, Felt252::from(7 * 3));          // index 7
        map.insert(blake2::FUN.0, Felt252::from(8 * 3));         // index 8
        map.insert(kzg_point_evaluation::ADDRESS, Felt252::from(9 * 3));    // index 10
        map
    };
}

#[allow(non_snake_case)]
pub fn bytes__eq__() -> Hint {
    Hint::new(
        String::from("Bytes__eq__"),
        |vm: &mut VirtualMachine,
         _exec_scopes: &mut ExecutionScopes,
         ids_data: &HashMap<String, HintReference>,
         ap_tracking: &ApTracking,
         _constants: &HashMap<String, Felt252>|
         -> Result<(), HintError> {
            let get_bytes_params = |name: &str| -> Result<
                (usize, cairo_vm::types::relocatable::Relocatable),
                HintError,
            > {
                let ptr = get_ptr_from_var_name(name, vm, ids_data, ap_tracking)?;
                let len_addr = (ptr + 1)?;

                let len_felt = vm.get_integer(len_addr)?.into_owned();
                let len = len_felt
                    .try_into()
                    .map_err(|_| MathError::Felt252ToUsizeConversion(Box::new(len_felt)))?;

                let data = vm.get_relocatable(ptr)?;

                Ok((len, data))
            };

            let (self_len, self_data) = get_bytes_params("_self")?;
            let (other_len, other_data) = get_bytes_params("other")?;

            // Compare bytes until we find a difference
            for i in 0..std::cmp::min(self_len, other_len) {
                let self_byte = vm.get_integer((self_data + i)?)?.into_owned();

                let other_byte = vm.get_integer((other_data + i)?)?.into_owned();

                if self_byte != other_byte {
                    // Found difference - set is_diff=1 and diff_index=i
                    insert_value_from_var_name(
                        "is_diff",
                        MaybeRelocatable::from(1),
                        vm,
                        ids_data,
                        ap_tracking,
                    )?;
                    insert_value_from_var_name(
                        "diff_index",
                        MaybeRelocatable::from(i),
                        vm,
                        ids_data,
                        ap_tracking,
                    )?;
                    return Ok(());
                }
            }

            // No differences found in common prefix
            // Lengths were checked before this hint
            insert_value_from_var_name(
                "is_diff",
                MaybeRelocatable::from(0),
                vm,
                ids_data,
                ap_tracking,
            )?;
            insert_value_from_var_name(
                "diff_index",
                MaybeRelocatable::from(0),
                vm,
                ids_data,
                ap_tracking,
            )?;
            Ok(())
        },
    )
}

pub fn b_le_a() -> Hint {
    Hint::new(
        String::from("b_le_a"),
        |vm: &mut VirtualMachine,
         _exec_scopes: &mut ExecutionScopes,
         ids_data: &HashMap<String, HintReference>,
         ap_tracking: &ApTracking,
         _constants: &HashMap<String, Felt252>|
         -> Result<(), HintError> {
            let a = get_integer_from_var_name("a", vm, ids_data, ap_tracking)?;
            let b = get_integer_from_var_name("b", vm, ids_data, ap_tracking)?;
            let result = usize::from(b <= a);
            insert_value_from_var_name(
                "is_min_b",
                MaybeRelocatable::from(result),
                vm,
                ids_data,
                ap_tracking,
            )?;
            Ok(())
        },
    )
}

pub fn fp_plus_2_or_0() -> Hint {
    Hint::new(
        String::from("fp_plus_2_or_0"),
        |vm: &mut VirtualMachine,
         _exec_scopes: &mut ExecutionScopes,
         _ids_data: &HashMap<String, HintReference>,
         _ap_tracking: &ApTracking,
         _constants: &HashMap<String, Felt252>|
         -> Result<(), HintError> {
            let fp_offset = (vm.get_fp() + 2)?;
            let value_set = vm.get_maybe(&fp_offset);
            if value_set.is_none() {
                vm.insert_value(fp_offset, MaybeRelocatable::from(0))?;
            }
            Ok(())
        },
    )
}

pub fn nibble_remainder() -> Hint {
    Hint::new(
        String::from("memory[fp + 2] = to_felt_or_relocatable(ids.x.value.len % 2)"),
        |vm: &mut VirtualMachine,
         _exec_scopes: &mut ExecutionScopes,
         ids_data: &HashMap<String, HintReference>,
         ap_tracking: &ApTracking,
         _constants: &HashMap<String, Felt252>|
         -> Result<(), HintError> {
            let bytes_ptr = get_ptr_from_var_name("x", vm, ids_data, ap_tracking)?;
            let len = vm.get_integer((bytes_ptr + 1)?)?.into_owned();
            let len: usize =
                len.try_into().map_err(|_| MathError::Felt252ToUsizeConversion(Box::new(len)))?;
            let remainder = len % 2;
            vm.insert_value((vm.get_fp() + 2)?, MaybeRelocatable::from(remainder))?;
            Ok(())
        },
    )
}

pub fn print_maybe_relocatable() -> Hint {
    Hint::new(
        String::from("print_maybe_relocatable"),
        |vm: &mut VirtualMachine,
         _exec_scopes: &mut ExecutionScopes,
         ids_data: &HashMap<String, HintReference>,
         ap_tracking: &ApTracking,
         _constants: &HashMap<String, Felt252>|
         -> Result<(), HintError> {
            let maybe_relocatable =
                get_maybe_relocatable_from_var_name("x", vm, ids_data, ap_tracking)?;
            println!("maybe_relocatable: {:?}", maybe_relocatable);
            Ok(())
        },
    )
}

pub fn precompile_index_from_address() -> Hint {
    Hint::new(
        String::from("precompile_index_from_address"),
        |vm: &mut VirtualMachine,
         _exec_scopes: &mut ExecutionScopes,
         ids_data: &HashMap<String, HintReference>,
         ap_tracking: &ApTracking,
         _constants: &HashMap<String, Felt252>|
         -> Result<(), HintError> {
            let address_felt = get_integer_from_var_name("address", vm, ids_data, ap_tracking)?;

            let address = Address::from({
                let bytes = address_felt.to_bytes_le();
                let mut address_bytes = [0u8; 20];
                address_bytes.copy_from_slice(&bytes[..20]);
                address_bytes
            });

            let index = PRECOMPILE_INDICES.get(&address).ok_or(HintError::CustomHint(
                Box::from(format!("Invalid precompile address: {:?}", address)),
            ))?;

            insert_value_from_var_name(
                "index",
                MaybeRelocatable::from(*index),
                vm,
                ids_data,
                ap_tracking,
            )?;
            Ok(())
        },
    )
}
