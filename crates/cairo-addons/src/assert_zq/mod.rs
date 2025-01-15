use lazy_static::lazy_static;
use serde_json::json;
use std::{collections::HashMap, fs::File, io::Write, sync::Mutex};

// Global state to track assertions, memory and allocation pointer
lazy_static! {
    static ref ASSERTION_COUNT: Mutex<usize> = Mutex::new(0);
    static ref MEMORY: Mutex<HashMap<usize, i64>> = Mutex::new(HashMap::new());
    static ref AP: Mutex<usize> = Mutex::new(0);
    static ref ASSERTION_HISTORY: Mutex<Vec<String>> = Mutex::new(Vec::new());
    static ref STATE_DUMPER: Mutex<Option<StateDumper>> = Mutex::new(None);
    static ref VARIABLE_LOCATIONS: Mutex<HashMap<String, usize>> = Mutex::new(HashMap::new());
}

// Structure that implements Drop to automatically dump state
struct StateDumper;

impl Drop for StateDumper {
    fn drop(&mut self) {
        if let Err(e) = dump_state() {
            eprintln!("Failed to dump state: {}", e);
        }
    }
}

/// Ensures the state dumper is initialized
fn ensure_state_dumper() {
    let mut dumper = STATE_DUMPER.lock().unwrap();
    if dumper.is_none() {
        *dumper = Some(StateDumper);
    }
}

/// Increments the global assertion counter and returns its new value
fn increment_assertion_count() -> usize {
    let mut count = ASSERTION_COUNT.lock().unwrap();
    *count += 1;
    *count
}

/// Gets the current allocation pointer value
pub(crate) fn get_ap() -> usize {
    *AP.lock().unwrap()
}

/// Increments the allocation pointer and returns the previous value
fn increment_ap() -> usize {
    let mut ap = AP.lock().unwrap();
    let prev_ap = *ap;
    *ap += 1;
    prev_ap
}

/// Stores a value in memory at the given address
pub(crate) fn store_in_memory(addr: usize, value: i64) {
    let mut memory = MEMORY.lock().unwrap();
    memory.insert(addr, value);
}

/// Gets a value from memory at the given address
pub(crate) fn get_from_memory(addr: usize) -> Option<i64> {
    let memory = MEMORY.lock().unwrap();
    memory.get(&addr).copied()
}

/// Records a raw assertion string in the history
pub(crate) fn record_assertion(raw_str: String) {
    ensure_state_dumper();
    let mut history = ASSERTION_HISTORY.lock().unwrap();
    history.push(raw_str);
}

/// Gets the complete assertion history
pub fn get_assertion_history() -> Vec<String> {
    let history = ASSERTION_HISTORY.lock().unwrap();
    history.clone()
}

/// Gets the location of a variable if it exists
pub(crate) fn get_variable_location(name: &str) -> Option<usize> {
    let vars = VARIABLE_LOCATIONS.lock().unwrap();
    vars.get(name).copied()
}

/// Records a variable's location
pub(crate) fn record_variable_location(name: String, location: usize) {
    let mut vars = VARIABLE_LOCATIONS.lock().unwrap();
    vars.insert(name, location);
}

/// Resets all global state
pub fn reset_state() {
    let mut count = ASSERTION_COUNT.lock().unwrap();
    *count = 0;
    let mut memory = MEMORY.lock().unwrap();
    memory.clear();
    let mut ap = AP.lock().unwrap();
    *ap = 0;
    let mut history = ASSERTION_HISTORY.lock().unwrap();
    history.clear();
    let mut vars = VARIABLE_LOCATIONS.lock().unwrap();
    vars.clear();
}

/// Dumps the assertion history to program.cairo and memory state to memory.json
pub fn dump_state() -> std::io::Result<()> {
    // Dump assertions to program.cairo
    let history = ASSERTION_HISTORY.lock().unwrap();
    let mut program_file = File::create("program.cairo")?;
    for assertion in history.iter() {
        writeln!(program_file, "{}", assertion)?;
    }

    // Dump memory to memory.json
    let memory = MEMORY.lock().unwrap();
    let memory_json = json!({
        "ap": *AP.lock().unwrap(),
        "memory": memory.iter().collect::<HashMap<_, _>>()
    });
    let mut memory_file = File::create("memory.json")?;
    writeln!(memory_file, "{}", serde_json::to_string_pretty(&memory_json)?)?;

    Ok(())
}

/// Verifies that a value in memory matches the expected value, or stores it if it doesn't exist
pub(crate) fn verify_memory(addr: usize, expected: i64, context: &str) {
    if let Some(actual) = get_from_memory(addr) {
        if actual != expected {
            panic!(
                "Assertion failed: memory at address {} contains {} but expected {} ({})",
                addr, actual, expected, context
            );
        }
    } else {
        // If no value exists at this address, store the expected value
        store_in_memory(addr, expected);
    }
}

/// A macro for zero-knowledge assertions that maintains global state
#[macro_export]
macro_rules! assert_zq {
    // Multiple assertions
    (
        assert $var:ident = $value:expr;
        $($rest:tt)*
    ) => {{
        // Check if the variable exists in memory
        let var_location = $crate::assert_zq::get_variable_location(stringify!($var));

        match var_location {
            Some(location) => {
                // Variable exists, verify the value
                let value = $value as i64;
                $crate::assert_zq::verify_memory(location, value, &format!("{} = {}", stringify!($var), stringify!($value)));
                $crate::assert_zq::record_assertion(format!(
                    "assert {} = {};",
                    stringify!($var),
                    stringify!($value)
                ));
            }
            None => {
                // Variable doesn't exist, try to get it from scope
                let count = $crate::assert_zq::increment_assertion_count();
                let ap = $crate::assert_zq::increment_ap();
                let value = $value as i64;
                $crate::assert_zq::store_in_memory(ap, value);
                $crate::assert_zq::record_variable_location(stringify!($var).to_string(), ap);
                $crate::assert_zq::record_assertion(format!(
                    "tempvar {};\nassert {} = {};",
                    stringify!($var),
                    stringify!($var),
                    stringify!($value)
                ));
                println!(
                    "Assertion #{}: Stored {} = {} at address {}",
                    count,
                    stringify!($var),
                    value,
                    ap
                );
            }
        }
        assert_zq!($($rest)*);
    }};

    // Multiple assertions with memory[ap]
    (
        assert memory[ap] = $value:expr;
        $($rest:tt)*
    ) => {{
        let count = $crate::assert_zq::increment_assertion_count();
        let ap = $crate::assert_zq::get_ap();
        let value = $value as i64;
        $crate::assert_zq::store_in_memory(ap, value);
        $crate::assert_zq::verify_memory(ap, value, &format!("memory[ap] = {}", stringify!($value)));
        $crate::assert_zq::record_assertion(format!("assert memory[ap] = {}", stringify!($value)));
        println!("Assertion #{}: Stored memory[ap] = {} at address {}", count, value, ap);
        assert_zq!($($rest)*);
    }};

    // Multiple assertions with memory[ap + offset]
    (
        assert memory[ap + $offset:expr] = $value:expr;
        $($rest:tt)*
    ) => {{
        let count = $crate::assert_zq::increment_assertion_count();
        let ap = $crate::assert_zq::get_ap();
        let addr = ap + ($offset as usize);
        let value = $value as i64;
        $crate::assert_zq::store_in_memory(addr, value);
        $crate::assert_zq::verify_memory(addr, value, &format!("memory[ap + {}] = {}", stringify!($offset), stringify!($value)));
        $crate::assert_zq::record_assertion(format!(
            "assert memory[ap + {}] = {}",
            stringify!($offset),
            stringify!($value)
        ));
        println!(
            "Assertion #{}: Stored memory[ap + {}] = {} at address {}",
            count, $offset, value, addr
        );
        assert_zq!($($rest)*);
    }};

    // Multiple assertions with memory[ap - offset]
    (
        assert memory[ap - $offset:expr] = $value:expr;
        $($rest:tt)*
    ) => {{
        let count = $crate::assert_zq::increment_assertion_count();
        let ap = $crate::assert_zq::get_ap();
        let addr = ap.checked_sub($offset as usize).expect("AP offset underflow");
        let value = $value as i64;
        $crate::assert_zq::store_in_memory(addr, value);
        $crate::assert_zq::verify_memory(addr, value, &format!("memory[ap - {}] = {}", stringify!($offset), stringify!($value)));
        $crate::assert_zq::record_assertion(format!(
            "assert memory[ap - {}] = {}",
            stringify!($offset),
            stringify!($value)
        ));
        println!(
            "Assertion #{}: Stored memory[ap - {}] = {} at address {}",
            count, $offset, value, addr
        );
        assert_zq!($($rest)*);
    }};

    // Multiple assertions with memory[expr]
    (
        assert memory[$addr:expr] = $value:expr;
        $($rest:tt)*
    ) => {{
        let count = $crate::assert_zq::increment_assertion_count();
        let addr = $addr;
        let value = $value as i64;
        $crate::assert_zq::store_in_memory(addr, value);
        $crate::assert_zq::verify_memory(addr, value, &format!("memory[{}] = {}", stringify!($addr), stringify!($value)));
        $crate::assert_zq::record_assertion(format!(
            "assert memory[{}] = {}",
            stringify!($addr),
            stringify!($value)
        ));
        println!("Assertion #{}: Stored memory[{}] = {}", count, addr, value);
        assert_zq!($($rest)*);
    }};

    // Base cases (single assertions)
    (assert $var:ident = $value:expr) => {{
        let count = $crate::assert_zq::increment_assertion_count();
        let ap = $crate::assert_zq::increment_ap();
        let value = $value as i64;
        $crate::assert_zq::store_in_memory(ap, value);
        $crate::assert_zq::verify_memory(ap, value, &format!("{} = {}", stringify!($var), stringify!($value)));
        $crate::assert_zq::record_assertion(format!(
            "tempvar {};\nassert {} = {};",
            stringify!($var),
            stringify!($var),
            stringify!($value)
        ));
        println!(
            "Assertion #{}: Stored {} = {} at address {}",
            count,
            stringify!($var),
            value,
            ap
        );
    }};

    (assert memory[ap] = $value:expr) => {{
        let count = $crate::assert_zq::increment_assertion_count();
        let ap = $crate::assert_zq::get_ap();
        let value = $value as i64;
        $crate::assert_zq::store_in_memory(ap, value);
        $crate::assert_zq::verify_memory(ap, value, &format!("memory[ap] = {}", stringify!($value)));
        $crate::assert_zq::record_assertion(format!("assert memory[ap] = {}", stringify!($value)));
        println!("Assertion #{}: Stored memory[ap] = {} at address {}", count, value, ap);
    }};

    (assert memory[ap + $offset:expr] = $value:expr) => {{
        let count = $crate::assert_zq::increment_assertion_count();
        let ap = $crate::assert_zq::get_ap();
        let addr = ap + ($offset as usize);
        let value = $value as i64;
        $crate::assert_zq::store_in_memory(addr, value);
        $crate::assert_zq::verify_memory(addr, value, &format!("memory[ap + {}] = {}", stringify!($offset), stringify!($value)));
        $crate::assert_zq::record_assertion(format!(
            "assert memory[ap + {}] = {}",
            stringify!($offset),
            stringify!($value)
        ));
        println!(
            "Assertion #{}: Stored memory[ap + {}] = {} at address {}",
            count, $offset, value, addr
        );
    }};

    (assert memory[ap - $offset:expr] = $value:expr) => {{
        let count = $crate::assert_zq::increment_assertion_count();
        let ap = $crate::assert_zq::get_ap();
        let addr = ap.checked_sub($offset as usize).expect("AP offset underflow");
        let value = $value as i64;
        $crate::assert_zq::store_in_memory(addr, value);
        $crate::assert_zq::verify_memory(addr, value, &format!("memory[ap - {}] = {}", stringify!($offset), stringify!($value)));
        $crate::assert_zq::record_assertion(format!(
            "assert memory[ap - {}] = {}",
            stringify!($offset),
            stringify!($value)
        ));
        println!(
            "Assertion #{}: Stored memory[ap - {}] = {} at address {}",
            count, $offset, value, addr
        );
    }};

    (assert memory[$addr:expr] = $value:expr) => {{
        let count = $crate::assert_zq::increment_assertion_count();
        let addr = $addr;
        let value = $value as i64;
        $crate::assert_zq::store_in_memory(addr, value);
        $crate::assert_zq::verify_memory(addr, value, &format!("memory[{}] = {}", stringify!($addr), stringify!($value)));
        $crate::assert_zq::record_assertion(format!(
            "assert memory[{}] = {}",
            stringify!($addr),
            stringify!($value)
        ));
        println!("Assertion #{}: Stored memory[{}] = {}", count, addr, value);
    }};

    // Empty case
    () => {};
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    // Helper function to clean up test files
    fn cleanup_test_files() {
        let _ = fs::remove_file("program.cairo");
        let _ = fs::remove_file("memory.json");
    }

    #[test]
    fn test_automatic_state_dumping() {
        cleanup_test_files();

        {
            reset_state();
            // Make assertions in a single call
            assert_zq!(
                assert x = 10;
                assert memory[ap] = 20;
                assert memory[ap + 1] = 30;
            );
            // Don't call dump_state() explicitly
        } // StateDumper will be dropped here

        // Verify program.cairo was created automatically
        let program_contents = fs::read_to_string("program.cairo").unwrap();
        assert_eq!(
            program_contents,
            "tempvar x;\nassert x = 10;\nassert memory[ap] = 20\nassert memory[ap + 1] = 30\n"
        );

        // Verify memory.json was created automatically
        let memory_contents = fs::read_to_string("memory.json").unwrap();
        let memory_json: serde_json::Value = serde_json::from_str(&memory_contents).unwrap();

        assert_eq!(memory_json["ap"], 1);
        assert_eq!(memory_json["memory"]["0"], 10);
        assert_eq!(memory_json["memory"]["1"], 20);
        assert_eq!(memory_json["memory"]["2"], 30);

        cleanup_test_files();
    }

    #[test]
    fn test_multiple_variable_assignments() {
        reset_state();
        assert_zq!(
            assert x = 10;
            assert y = 20;
            assert z = 30;
        );

        // Verify values were stored at consecutive addresses
        assert_eq!(get_from_memory(0), Some(10));
        assert_eq!(get_from_memory(1), Some(20));
        assert_eq!(get_from_memory(2), Some(30));
        // Verify AP was incremented thrice
        assert_eq!(get_ap(), 3);
        // Verify assertion count
        assert_eq!(*ASSERTION_COUNT.lock().unwrap(), 3);
        // Verify assertion history with tempvars
        assert_eq!(
            get_assertion_history(),
            vec![
                "tempvar x;\nassert x = 10;",
                "tempvar y;\nassert y = 20;",
                "tempvar z;\nassert z = 30;"
            ]
        );
    }

    #[test]
    fn test_mixed_assignments() {
        reset_state();
        assert_zq!(
            assert x = 10;
            assert memory[ap] = 20;
            assert memory[ap + 1] = 30;
            assert y = 40;
        );

        // Verify values were stored correctly
        assert_eq!(get_from_memory(0), Some(10)); // x
        assert_eq!(get_from_memory(1), Some(20)); // memory[ap]
        assert_eq!(get_from_memory(2), Some(30)); // memory[ap + 1]
        assert_eq!(get_from_memory(3), Some(40)); // y

        // Verify AP was incremented twice (once for each variable)
        assert_eq!(get_ap(), 2);

        // Verify assertion history
        assert_eq!(
            get_assertion_history(),
            vec![
                "tempvar x;\nassert x = 10;",
                "assert memory[ap] = 20",
                "assert memory[ap + 1] = 30",
                "tempvar y;\nassert y = 40;"
            ]
        );
    }

    #[test]
    fn test_memory_assignment() {
        reset_state();
        assert_zq!(assert x = 10);

        // Verify the value was stored at address 0
        assert_eq!(get_from_memory(0), Some(10));
        // Verify AP was incremented
        assert_eq!(get_ap(), 1);
        // Verify assertion count
        assert_eq!(*ASSERTION_COUNT.lock().unwrap(), 1);
        // Verify assertion history with tempvar
        assert_eq!(get_assertion_history(), vec!["tempvar x;\nassert x = 10;"]);
    }

    #[test]
    fn test_multiple_assignments() {
        reset_state();
        assert_zq!(assert x = 10);
        assert_zq!(assert y = 20);

        // Verify values were stored at consecutive addresses
        assert_eq!(get_from_memory(0), Some(10));
        assert_eq!(get_from_memory(1), Some(20));
        // Verify AP was incremented twice
        assert_eq!(get_ap(), 2);
        // Verify assertion count
        assert_eq!(*ASSERTION_COUNT.lock().unwrap(), 2);
        // Verify assertion history with tempvars
        assert_eq!(
            get_assertion_history(),
            vec!["tempvar x;\nassert x = 10;", "tempvar y;\nassert y = 20;"]
        );
    }

    #[test]
    fn test_direct_memory_assignment() {
        reset_state();
        assert_zq!(assert memory[0] = 42);
        assert_zq!(assert memory[1] = 43);

        // Verify values were stored at specified addresses
        assert_eq!(get_from_memory(0), Some(42));
        assert_eq!(get_from_memory(1), Some(43));
        // Verify AP wasn't modified
        assert_eq!(get_ap(), 0);
        // Verify assertion history (no tempvars needed)
        assert_eq!(get_assertion_history(), vec!["assert memory[0] = 42", "assert memory[1] = 43"]);
    }

    #[test]
    fn test_ap_memory_assignment() {
        reset_state();
        assert_zq!(assert memory[ap] = 100);

        // Verify value was stored at AP (0)
        assert_eq!(get_from_memory(0), Some(100));
        // Verify AP wasn't modified
        assert_eq!(get_ap(), 0);
        // Verify assertion history (no tempvar needed)
        assert_eq!(get_assertion_history(), vec!["assert memory[ap] = 100"]);
    }

    #[test]
    fn test_ap_offset_memory_assignment() {
        reset_state();
        // Set AP to 5 for testing
        for _ in 0..5 {
            increment_ap();
        }

        assert_zq!(assert memory[ap + 1] = 100); // Store at 6
        assert_zq!(assert memory[ap - 2] = 200); // Store at 3

        // Verify values were stored at correct offsets
        assert_eq!(get_from_memory(6), Some(100));
        assert_eq!(get_from_memory(3), Some(200));
        // Verify AP wasn't modified
        assert_eq!(get_ap(), 5);
        // Verify assertion history (no tempvars needed)
        assert_eq!(
            get_assertion_history(),
            vec!["assert memory[ap + 1] = 100", "assert memory[ap - 2] = 200"]
        );
    }

    #[test]
    #[should_panic(expected = "AP offset underflow")]
    fn test_ap_negative_offset_underflow() {
        reset_state();
        // AP is 0, so ap - 1 should panic
        assert_zq!(assert memory[ap - 1] = 100);
    }

    #[test]
    fn test_complex_expressions() {
        reset_state();
        let offset = 5;
        assert_zq!(assert memory[ap + offset] = 42);
        assert_zq!(assert memory[ap + (2 * 3)] = 43);

        // Verify assertion history preserves the raw expressions (no tempvars needed)
        assert_eq!(
            get_assertion_history(),
            vec!["assert memory[ap + offset] = 42", "assert memory[ap + (2 * 3)] = 43"]
        );
    }

    #[test]
    fn test_variable_declarations() {
        reset_state();
        assert_zq!(assert x = 10);
        assert_zq!(assert y = 20);
        assert_zq!(assert z = 30);

        // Verify each variable assignment includes a tempvar declaration
        assert_eq!(
            get_assertion_history(),
            vec![
                "tempvar x;\nassert x = 10;",
                "tempvar y;\nassert y = 20;",
                "tempvar z;\nassert z = 30;"
            ]
        );
    }

    #[test]
    #[should_panic(
        expected = "Assertion failed: memory at address 0 contains 20 but expected 10 (x = 10)"
    )]
    fn test_failed_variable_assertion() {
        reset_state();
        // First store 20 at address 0
        store_in_memory(0, 20);
        // Then try to assert it should be 10
        assert_zq!(assert x = 10);
    }

    #[test]
    #[should_panic(
        expected = "Assertion failed: memory at address 0 contains 10 but expected 20 (memory[ap] = 20)"
    )]
    fn test_failed_memory_assertion() {
        reset_state();
        // First store 10 at address 0
        store_in_memory(0, 10);
        // Then try to assert it should be 20
        assert_zq!(assert memory[ap] = 20);
    }

    #[test]
    #[should_panic(
        expected = "Assertion failed: memory at address 1 contains 30 but expected 20 (memory[ap + 1] = 20)"
    )]
    fn test_failed_offset_assertion() {
        reset_state();
        // First store 30 at address 1
        store_in_memory(1, 30);
        // Then try to assert it should be 20
        assert_zq!(assert memory[ap + 1] = 20);
    }

    #[test]
    #[should_panic(
        expected = "Assertion failed: no value at address 5 where 10 was expected (memory[5] = 10)"
    )]
    fn test_failed_missing_value() {
        reset_state();
        // Try to assert a value at an address that hasn't been written to
        assert_zq!(assert memory[5] = 10);
    }

    #[test]
    fn test_multiple_assertions_fail_fast() {
        reset_state();

        // This should panic on the second assertion
        let result = std::panic::catch_unwind(|| {
            assert_zq!(
                assert x = 10;  // This will succeed
                assert y = 20;  // This will fail because x's value is at y's location
                assert z = 30;  // This won't be reached
            );
        });

        assert!(result.is_err());
        let err = result.unwrap_err();
        let err_msg = err.downcast_ref::<String>().unwrap();
        assert!(err_msg
            .contains("Assertion failed: no value at address 1 where 20 was expected (y = 20)"));
    }

    #[test]
    fn test_assert_missing_value() {
        reset_state();
        // Try to assert a value at an address that hasn't been written to
        assert_zq!(assert memory[5] = 10);

        // Verify the value was stored
        assert_eq!(get_from_memory(5), Some(10));
        assert_eq!(get_assertion_history(), vec!["assert memory[5] = 10"]);
    }

    #[test]
    fn test_multiple_assertions_store_missing() {
        reset_state();

        assert_zq!(
            assert x = 10;      // This will store at ap (0)
            assert y = 20;      // This will store at ap (1)
            assert memory[5] = 30;  // This will store at 5
            assert memory[ap + 2] = 40;  // This will store at 3
        );

        // Verify all values were stored
        assert_eq!(get_from_memory(0), Some(10)); // x
        assert_eq!(get_from_memory(1), Some(20)); // y
        assert_eq!(get_from_memory(5), Some(30)); // direct memory access
        assert_eq!(get_from_memory(3), Some(40)); // ap + 2

        // Verify assertion history
        assert_eq!(
            get_assertion_history(),
            vec![
                "tempvar x;\nassert x = 10;",
                "tempvar y;\nassert y = 20;",
                "assert memory[5] = 30",
                "assert memory[ap + 2] = 40"
            ]
        );
    }

    #[test]
    #[should_panic(
        expected = "Assertion failed: memory at address 5 contains 20 but expected 10 (memory[5] = 10)"
    )]
    fn test_overwrite_existing_value() {
        reset_state();
        // First store a value
        store_in_memory(5, 20);
        // Then try to assert a different value
        assert_zq!(assert memory[5] = 10);
    }

    #[test]
    fn test_variable_reuse() {
        reset_state();

        // First use of x
        assert_zq!(assert x = 10);

        // Second use of x should not create a new tempvar
        assert_zq!(assert x = 10);

        // Verify assertion history
        assert_eq!(
            get_assertion_history(),
            vec![
                "tempvar x;\nassert x = 10;", // First use includes tempvar
                "assert x = 10;"              // Second use doesn't
            ]
        );

        // Verify memory and AP
        assert_eq!(get_from_memory(0), Some(10));
        assert_eq!(get_ap(), 1); // AP should only increment once
    }

    #[test]
    #[should_panic(expected = "Assertion failed: memory at address 0 contains 10 but expected 20")]
    fn test_variable_reuse_different_value() {
        reset_state();

        assert_zq!(assert x = 10);
        assert_zq!(assert x = 20); // Should panic as x is already 10
    }

    #[test]
    fn test_multiple_variable_reuse() {
        reset_state();

        assert_zq!(
            assert x = 10;
            assert y = 20;
            assert x = 10;  // Reuse x
            assert z = 30;
            assert y = 20;  // Reuse y
        );

        // Verify assertion history
        assert_eq!(
            get_assertion_history(),
            vec![
                "tempvar x;\nassert x = 10;",
                "tempvar y;\nassert y = 20;",
                "assert x = 10;",
                "tempvar z;\nassert z = 30;",
                "assert y = 20;"
            ]
        );

        // Verify memory and AP
        assert_eq!(get_from_memory(0), Some(10)); // x
        assert_eq!(get_from_memory(1), Some(20)); // y
        assert_eq!(get_from_memory(2), Some(30)); // z
        assert_eq!(get_ap(), 3); // AP should increment only for new variables
    }

    #[test]
    fn test_rust_scope_variable() {
        reset_state();

        let rust_var = 43;
        assert_zq!(assert rust_var = 42);

        // Verify assertion history
        assert_eq!(get_assertion_history(), vec!["tempvar rust_var;\nassert rust_var = 42;"]);

        // Verify memory and AP
        assert_eq!(get_from_memory(0), Some(42));
        assert_eq!(get_ap(), 1);
    }

    #[test]
    fn test_mixed_scope_and_reuse() {
        reset_state();

        let rust_var = 42;
        assert_zq!(
            assert x = 10;
            assert rust_var = 42;
            assert x = 10;      // Reuse x
            assert rust_var = 42;  // Reuse rust_var
        );

        // Verify assertion history
        assert_eq!(
            get_assertion_history(),
            vec![
                "tempvar x;\nassert x = 10;",
                "tempvar rust_var;\nassert rust_var = 42;",
                "assert x = 10;",
                "assert rust_var = 42;"
            ]
        );

        // Verify memory and AP
        assert_eq!(get_from_memory(0), Some(10)); // x
        assert_eq!(get_from_memory(1), Some(42)); // rust_var
        assert_eq!(get_ap(), 2); // AP should increment only for new variables
    }
}
