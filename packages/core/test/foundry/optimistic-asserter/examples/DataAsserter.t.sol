// SPDX-License-Identifier: AGPL-3.0-only
pragma solidity ^0.8.0;
import "../CommonOptimisticAsserterTest.sol";
import "../../../../contracts/optimistic-asserter/implementation/examples/DataAsserter.sol";

contract DataAsserterTest is CommonOptimisticAsserterTest {
    DataAsserter public dataAsserter;
    bytes32 dataId = bytes32("dataId");
    bytes32 correctData = bytes32("correctData");
    bytes32 incorrectData = bytes32("incorrectData");

    function setUp() public {
        _commonSetup();
        dataAsserter = new DataAsserter(address(defaultCurrency), address(optimisticAsserter));
    }

    function test_DataAssertionNoDispute() public {
        // Assert data.
        vm.startPrank(TestAddress.account1);
        defaultCurrency.allocateTo(TestAddress.account1, optimisticAsserter.getMinimumBond(address(defaultCurrency)));
        defaultCurrency.approve(address(dataAsserter), optimisticAsserter.getMinimumBond(address(defaultCurrency)));
        bytes32 assertionId = dataAsserter.assertDataFor(dataId, correctData, TestAddress.account1);
        vm.stopPrank(); // Return caller address to standard.

        // Assertion data should not be available before the liveness period.
        (bool dataAvailable, bytes32 data) = dataAsserter.getData(assertionId);
        assertFalse(dataAvailable);

        // Move time forward to allow for the assertion to expire.
        timer.setCurrentTime(timer.getCurrentTime() + dataAsserter.assertionLiveness());

        // Settle the assertion.
        optimisticAsserter.settleAssertion(assertionId);

        // Data should now be available.
        (dataAvailable, data) = dataAsserter.getData(assertionId);
        assertTrue(dataAvailable);
        assertEq(data, correctData);
    }

    function test_DataAssertionWithWrongDispute() public {
        // Assert data.
        vm.startPrank(TestAddress.account1);
        defaultCurrency.allocateTo(TestAddress.account1, optimisticAsserter.getMinimumBond(address(defaultCurrency)));
        defaultCurrency.approve(address(dataAsserter), optimisticAsserter.getMinimumBond(address(defaultCurrency)));
        bytes32 assertionId = dataAsserter.assertDataFor(dataId, correctData, TestAddress.account1);
        vm.stopPrank(); // Return caller address to standard.

        // Dispute assertion with Account2 and DVM votes that the original assertion was true.
        OracleRequest memory oracleRequest = _disputeAndGetOracleRequest(assertionId, defaultBond);
        _mockOracleResolved(address(mockOracle), oracleRequest, true);
        assertTrue(optimisticAsserter.settleAndGetAssertionResult(assertionId));

        (bool dataAvailable, bytes32 data) = dataAsserter.getData(assertionId);
        assertTrue(dataAvailable);
        assertEq(data, correctData);
    }

    function test_DataAssertionWithCorrectDispute() public {
        // Assert data.
        vm.startPrank(TestAddress.account1);
        defaultCurrency.allocateTo(TestAddress.account1, optimisticAsserter.getMinimumBond(address(defaultCurrency)));
        defaultCurrency.approve(address(dataAsserter), optimisticAsserter.getMinimumBond(address(defaultCurrency)));
        bytes32 assertionId = dataAsserter.assertDataFor(dataId, incorrectData, TestAddress.account1);
        vm.stopPrank(); // Return caller address to standard.

        // Dispute assertion with Account2 and DVM votes that the original assertion was wrong.
        OracleRequest memory oracleRequest = _disputeAndGetOracleRequest(assertionId, defaultBond);
        _mockOracleResolved(address(mockOracle), oracleRequest, false);
        assertFalse(optimisticAsserter.settleAndGetAssertionResult(assertionId));

        // Check that the data assertion has been deleted
        (, , address asserter, ) = dataAsserter.assertionsData(assertionId);
        assertEq(asserter, address(0));

        (bool dataAvailable, bytes32 data) = dataAsserter.getData(assertionId);
        assertFalse(dataAvailable);

        // Increase time in the evm
        vm.warp(block.timestamp + 1);

        // Same asserter should be able to re-assert the correct data.
        vm.startPrank(TestAddress.account1);
        defaultCurrency.allocateTo(TestAddress.account1, optimisticAsserter.getMinimumBond(address(defaultCurrency)));
        defaultCurrency.approve(address(dataAsserter), optimisticAsserter.getMinimumBond(address(defaultCurrency)));
        bytes32 oaAssertionId2 = dataAsserter.assertDataFor(dataId, correctData, TestAddress.account1);
        vm.stopPrank(); // Return caller address to standard.

        // Move time forward to allow for the assertion to expire.
        timer.setCurrentTime(timer.getCurrentTime() + dataAsserter.assertionLiveness());

        // Settle the assertion.
        optimisticAsserter.settleAssertion(oaAssertionId2);

        // Data should now be available.
        (dataAvailable, data) = dataAsserter.getData(oaAssertionId2);
        assertTrue(dataAvailable);
        assertEq(data, correctData);
    }
}
