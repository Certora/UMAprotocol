// For every new spec you create, import this basic spec file:
import "./Asserter_Base.spec"
import "./dispatchedMethods.spec"

using TestnetERC20 as testERC20
/**************************************************
 *      Top Level Properties / Rule Ideas         *
 **************************************************/
// Here you can write your ideas for rules and implement them 
// in this spec.

/**************************************************
 *                  Misc. rules                   *
 **************************************************/

// A simple rule that checks which of the main contract methods
// are reachable (reach the assert false statement after function call).
 rule sanity(method f) {
    env e;  // Environment variable - includes all transaction and block information.
    calldataarg args; // arbitrary calldata - adapted for every method signature implicitly
    f(e, args);
    assert false;
}

// Checks that view functions in the contract never revert. 
rule viewFuncsDontRevert(method f) 
filtered{f -> f.isView} { // filters the methods to only view functions
    env e;
    require e.msg.value == 0;
    calldataarg args;
    f@withrevert(e, args);

    assert !lastReverted;
}

/**************************************************
 *  Function Integrity (Unit Testing) Rules       *
 **************************************************/
rule assertionDisputerIntegrity(address disputer, bytes32 assertionID) {
    env e;
    disputeAssertion(e, assertionID, disputer);
    assert disputer == getAssertionDisputer(assertionID);
}

/**************************************************
 *                 "Who changed" Rules            *
 **************************************************/
// This type of rules calls any of the main contract's public/external methods
// and checks whether a state variable was changed after the 
// invocation of this function.

rule whoChanged_cachedOracle(method f) 
filtered{f -> !f.isView} { // We filter out view functions as they do not change state variables.
    env e;
    calldataarg args;
    uint256 cachedOracle1 = cachedOracle();
        f(e, args);
    uint256 cachedOracle2 = cachedOracle();

    assert cachedOracle1 == cachedOracle2;
}

rule whoChanged_burnedBondPercentage(method f)
filtered{f -> !f.isView} {
    env e;
    calldataarg args;
    uint256 burnPer1 = burnedBondPercentage();
        f(e,args);
    uint256 burnPer2 = burnedBondPercentage();

    assert burnPer1 == burnPer2;
}

rule whoChanged_defaultCurrency(method f)
filtered{f -> !f.isView} {
    env e;
    calldataarg args;
    uint256 defaultCurrency1 = defaultCurrency();
        f(e,args);
    uint256 defaultCurrency2 = defaultCurrency();

    assert defaultCurrency1 == defaultCurrency2;
}

rule whoChanged_settlementResolution(method f, bytes32 ID)
filtered{f -> !f.isView} {
    env e;
    calldataarg args;
    bool res1 = getAssertionSettlementResolution(ID);
        f(e, args);
    bool res2 = getAssertionSettlementResolution(ID);

    assert res1 == res2;
}

rule whoChanged_assertionBond(method f, bytes32 ID)
filtered{f -> !f.isView && !isMultiCall(f)} {
    env e;
    calldataarg args;
    uint256 bond1 = getAssertionBond(ID);
        f(e, args);
    uint256 bond2 = getAssertionBond(ID);

    assert bond1 == bond2;
}

rule whoChanged_assertionCurrency(method f, bytes32 ID)
filtered{f -> !f.isView && !isMultiCall(f)} {
    env e;
    calldataarg args;
    address currency1 = getAssertionCurrency(ID);
        f(e, args);
    address currency2 = getAssertionCurrency(ID);

    assert currency1 == currency2;
}
