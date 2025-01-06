import pytest
from ethereum_types.numeric import U256
from hypothesis import given
from hypothesis import strategies as st

from ethereum.cancun.vm.exceptions import ExceptionalHalt
from ethereum.cancun.vm.instructions.keccak import keccak
from ethereum.cancun.vm.stack import push
from tests.utils.args_gen import Evm
from tests.utils.strategies import evm_lite


class TestKeccak:
    @given(
        evm=evm_lite,
        start_index=st.integers(min_value=0, max_value=128).map(U256),
        size=st.integers(min_value=0, max_value=32768).map(U256),
    )
    def test_keccak(self, cairo_run, evm: Evm, start_index: U256, size: U256):
        """
        Test the keccak instruction by comparing Cairo and Python implementations
        """
        push(evm.stack, start_index)
        push(evm.stack, size)
        try:
            cairo_result = cairo_run("keccak", evm)
        except ExceptionalHalt as cairo_error:
            with pytest.raises(type(cairo_error)):
                keccak(evm)
            return

        keccak(evm)
        assert evm == cairo_result
