// For every new spec you create, import this basic spec file:
import "./Asserter_Base.spec"
import "./dispatchedMethods.spec"

// An ERC20 contract in our scope. One can access its methods or address by
// its alias (testERC20)
using TestnetERC20 as testERC20
/**************************************************
 *      Top Level Properties / Rule Ideas         *
 **************************************************/
 // Prove that the sum of bonds for a specific currency is correlated with the 
 // main contract ERC20 balance. 

methods {
    // Added by Certora: a method to calculate the settlement fee for everty assertion.
    getOracleFeeByAssertion(bytes32) returns (uint256) envfree
    getDiscardOracleByAssertion(bytes32) returns (bool) envfree
    getOraclePrice(bytes32) returns (int256) envfree
}

/**************************************************
 *     Utilities for tracking the sum of bonds    *
 **************************************************/

definition maxAddress() returns address = 0xffffffffffffffffffffffffffffffffffffffff;
definition correctPrice() returns int256 = 1000000000000000000;
definition isDisputed(address d) returns bool = d!=0;


 // Ghost: the sum of bonds of all assertions for every ERC20 token.
ghost mapping(address => mathint) sumOfBonds {
    // An initial axiom for post-constructor state only.
    init_state axiom forall address token.
        sumOfBonds[token] == 0;
}

ghost mapping(address => mathint) sumOfOutstandingBonds {
init_state axiom forall address token.
sumOfOutstandingBonds[token] == 0;
}
 
// Ghost: tracks the currency token of each assertion by its ID.
ghost mapping(bytes32 => address) assertionToken {
    init_state axiom forall bytes32 assertionID.
        assertionToken[assertionID] == 0;
}

ghost mapping(bytes32 => address) assertionDisputer {
    init_state axiom forall bytes32 assertionID.
    assertionDisputer[assertionID] == 0;
}

ghost mapping(bytes32 => uint256) assertionBond {
    init_state axiom forall bytes32 assertionID.
    assertionBond[assertionID] == 0;
}

hook Sload uint256 bond assertions[KEY bytes32 assertionID].bond STORAGE{
    assertionBond[assertionID] = bond;
}

hook Sload address disputer assertions[KEY bytes32 assertionID].disputer STORAGE
{
    assertionDisputer[assertionID] = disputer & maxAddress();
}
// Hook : copy assertion currency to assertionToken
hook Sload address value assertions[KEY bytes32 assertionID].currency STORAGE 
{
    assertionToken[assertionID] = value & maxAddress();
} 

 // Hook : update sum of bonds per token
hook Sstore assertions[KEY bytes32 assertionID].bond uint256 value (uint256 old_value) STORAGE 
{
    address token = assertionToken[assertionID];
    sumOfBonds[token] = sumOfBonds[token] + value - old_value; 
    sumOfOutstandingBonds[token]= sumOfOutstandingBonds[token] + value - old_value; 
    assertionBond[assertionID] = value; //check whoChangedBond rule result to confirm that value only changes from 0 to a non zero value
}


// is it safe to assume that diputer is written to only during a dispute? whochanged rule to check what functions write to dispute
// don't need the value being written into diputer. can hook be  written without the "address disputer"
hook Sstore assertions[KEY bytes32 assertionID].disputer address disputer STORAGE
{
    uint256 bond = assertionBond[assertionID];
    address token = assertionToken[assertionID];
    sumOfOutstandingBonds[token] = sumOfOutstandingBonds[token] + bond;
    sumOfBonds[token] = sumOfBonds[token] + bond;
}

// to capture bond payout when an assertion is settled
// payout is the bond amount in case of an undisputed assertion and twice the  bond amount for a disputed assertion
// whochanged to see what functions write to the settled flag; is it only during settlement
hook Sstore assertions[KEY bytes32 assertionID].settled bool value (bool old_value) STORAGE
{
    address token = assertionToken[assertionID];
    address disputer = assertionDisputer[assertionID];
    bool disputed = isDisputed(disputer);
    uint256 bond = assertionBond[assertionID];
    sumOfOutstandingBonds[token] = disputed? sumOfOutstandingBonds[token] - 2* bond : sumOfOutstandingBonds[token] - bond;
    
}

invariant ghostTracksAssertionCurrency(bytes32 assertionID)
    assertionToken[assertionID] == getAssertionCurrency(assertionID)

/**************************************************/

// Verified
invariant validBondPercentage()
    burnedBondPercentage() <= 10^18 && burnedBondPercentage() > 0
    filtered{f -> !isMultiCall(f)}

// Simple integrity rule
rule assertionDisputerIntegrity(address disputer, bytes32 assertionID) {
    env e;
    disputeAssertion(e, assertionID, disputer);
    assert disputer == getAssertionDisputer(assertionID);
}

// When we call settleAssertion, we expect that either the asserter
// or the disputer get the correct amount of bonds.
rule onlyDisputerOrAsserterGetBond(bytes32 assertionID) {
    env e;
    address asserter = getAssertionAsserter(assertionID);
    address disputer = getAssertionDisputer(assertionID);
    address currency = getAssertionCurrency(assertionID);
    uint256 bond =  getAssertionBond(assertionID);
    address other;

    require currency == testERC20;  // A specific instance of the currency

    // 'Other' is none of the addresses involved in the bonds transfer.
    require asserter != other; 
    require disputer != other;
    require store != other;
    require currentContract != other;

    // Assuming the asserter is not the optimistic asserter contract.
    require asserter != currentContract;
    
    // Require zero fees (simplifcation)
    require getOracleFeeByAssertion(assertionID) == 0;

    uint256 asserterBalance1 = tokenBalanceOf(currency, asserter);
    uint256 disputerBalance1 = tokenBalanceOf(currency, disputer);
    uint256 otherBalance1 = tokenBalanceOf(currency, other);

        settleAssertion(e, assertionID);

    uint256 asserterBalance2 = tokenBalanceOf(currency, asserter);
    uint256 disputerBalance2 = tokenBalanceOf(currency, disputer);
    uint256 otherBalance2 = tokenBalanceOf(currency, other);

    // We first verify that no other address gets bonds
    assert otherBalance1 == otherBalance2;
    
    // Now we treat every possible case separately:
    if(disputer == 0) {
        bool asserterWins = (asserterBalance2 == asserterBalance1 + bond);
        bool asserterLoses = false;
        bool disputerWins = false;
        bool disputerLoses = true;
        assert (asserterWins && disputerLoses) || (disputerWins && asserterLoses);
    }
    else if(disputer == asserter) {
        bool asserterWins = (asserterBalance2 == asserterBalance1 + 2*bond);
        assert asserterWins;
    }
    else if(disputer == currentContract) {
        bool asserterWins = (asserterBalance2 == asserterBalance1 + 2*bond);
        bool disputerLoses = (disputerBalance1 == disputerBalance2 + 2*bond);
        bool asserterLoses = (asserterBalance2 == asserterBalance1);
        bool disputerWins= (disputerBalance1 == disputerBalance2);
        assert (asserterWins && disputerLoses) || (disputerWins && asserterLoses);
    }
    else {
        bool asserterWins = (asserterBalance2 == asserterBalance1 + 2*bond);
        bool asserterLoses = (asserterBalance2 == asserterBalance1);
        bool disputerWins = (disputerBalance2 == disputerBalance1 + 2*bond);
        bool disputerLoses = (disputerBalance1 == disputerBalance2);
        assert (asserterWins && disputerLoses) || (disputerWins && asserterLoses);
    }
}

// Verified
rule asserterBalanceDecreaseOnlyForSettle(address token, method f) 
filtered{f -> !f.isView && !isMultiCall(f)} {
    env e;
    calldataarg args;
    uint256 asserterBalanceBefore = tokenBalanceOf(token, currentContract);
        f(e, args);
    uint256 asserterBalanceAfter = tokenBalanceOf(token, currentContract);
    assert asserterBalanceBefore > asserterBalanceAfter => isSettle(f);
}

// Verified
rule asserterBalanceDecreaseLimitedByBond(bytes32 assertionId) {
    env e;
    address currency = getAssertionCurrency(assertionId);
    address token; require token != currency;
    uint256 bond = getAssertionBond(assertionId);
    uint256 asserterCurBalanceBefore = tokenBalanceOf(currency, currentContract);
    uint256 asserterTokBalanceBefore = tokenBalanceOf(token, currentContract);

        settleAssertion(e, assertionId);
    
    uint256 asserterCurBalanceAfter = tokenBalanceOf(currency, currentContract);
    uint256 asserterTokBalanceAfter = tokenBalanceOf(token, currentContract);

    assert asserterTokBalanceAfter == asserterTokBalanceBefore;
    assert asserterCurBalanceBefore <= 2*bond + asserterCurBalanceAfter;
}

// Tests our own ghosts : can ignore for now
rule testGhosts(bytes32 ID) {
    env e;
    calldataarg args;

    address token;
    uint256 bond1 = getAssertionBond(ID);
    address currency1 = getAssertionCurrency(ID);
    mathint sum1 = sumOfBonds[token];
        bytes32 assertionID = assertTruth(e, args);
    uint256 bond2 = getAssertionBond(ID);
    address currency2 = getAssertionCurrency(ID);
    mathint sum2 = sumOfBonds[token];

    require assertionID == ID;

    assert sum1 != sum2 => sum1 + bond2 - bond1 == to_mathint(sum2);
    assert assertionToken[ID] == currency2;
    assert sum1 != sum2 => token == currency2;
}

// Invariant to check that an assertion with discardOracle true should never have settlementResolution as true
// Verified
invariant discardOracleSettlementResolutionFalse(bytes32 assertionID)
getDiscardOracleByAssertion(assertionID) => !getAssertionSettlementResolution(assertionID)
    filtered{f -> !isMultiCall(f)} 
    {
        preserved{
            require getAssertionDisputer(assertionID) != 0;
        }
    }

// If the oracle says that the price in an assertion is wrong, then there should be no way for that assertion to be resolved as true
// Verified
invariant wrongPriceSettlementResolutionFalse(bytes32 assertionID)
getOraclePrice(assertionID) != correctPrice() => !getAssertionSettlementResolution(assertionID)
filtered{f -> !isMultiCall(f)} 
    {
        preserved{
            require getAssertionDisputer(assertionID) != 0;
        }
    }

// Invariant to check solvency of the contract
// WIP 
invariant tokenBalanceGESumOfOutstandingBonds(address token)
tokenBalanceOf(token, currentContract) >= sumOfOutstandingBonds[token]

// Rule to verify that an assertion, once settled, cannot be unsettled
// Verified
rule SettledAssertionCannotBeUnsettled(method f, env e)
filtered{f -> !isMultiCall(f)}
{
    bytes32 assertionID;
    bool _settled = getAssertionSettled(assertionID);
    address asserter = getAssertionAsserter(assertionID);
    calldataarg args;
    f(e, args);
    bool settled_ = getAssertionSettled(assertionID);
    assert asserter != 0 => (_settled => settled_),"An assertion cannot be unsettled";
}

// You can't have resolution with settlement
invariant resolutionOnlyIfSettled(bytes32 assertionID)
getAssertionSettlementResolution(assertionID) => getAssertionSettled(assertionID)
filtered{f -> !isMultiCall(f)} 


// Simple unit test for disputeAssertion function
// Verified
rule disputeAssetionTestRule(env e){
bytes32 assertionID;
address disputer;
address asserter = getAssertionAsserter(assertionID);
address disputerBefore = getAssertionDisputer(assertionID);
uint64 expirationTime = getAssertionExpirationTime(assertionID);

disputeAssertion(e, assertionID, disputer);

address disputerAfter = getAssertionDisputer(assertionID);

assert disputerBefore == 0,"Cannot dispute and already disputed assertion";
assert disputerAfter == disputer,"disputer should match the address supplied in the call";
assert e.block.timestamp < expirationTime,"dispute should be possible only before the expiration time";
assert asserter != 0,"cannot dispute  an assertion that doesn't exist";

}


rule disputeAssertionTest(env e){
    // state before
    bytes32 assertionID;
    address disputer;
    address disputerBefore = getAssertionDisputer(assertionID);
    uint64 expirationTime = getAssertionExpirationTime(assertionID);
    address asserter = getAssertionAsserter(assertionID);
    // require 

    // Function call
    disputeAssertion@withrevert(e, assertionID, disputer);
    bool successful = !lastReverted;
    // state after

    // assertions this about state change due to function
    assert successful => disputerBefore == 0,"can only dispute an assertion once";
    assert successful => e.block.timestamp < expirationTime,"can only dispute before expiration time";
    assert asserter == 0 => !successful,"assertion should exist";
    
}


rule whoChangedSettled(method f){
    env e;
    calldataarg args;
    bytes32 assertionID;
    bool _settled = getAssertionSettled(assertionID);
    f(e, args);
    bool settled_ = getAssertionSettled(assertionID);
    assert settled_ == _settled;

}

rule whoChangedBond(method f){
    env e;
    bytes32 assertionID;
    uint256 _bond = getAssertionBond(assertionID);
    calldataarg args;
    f(e, args);
    uint256 bond_ = getAssertionBond(assertionID);
    assert _bond == bond_;
    assert _bond != bond_ => _bond == 0 && bond_ > 0,"bond can only increase from 0 to some value";
}

rule enoughBalanceToCoverBondForAssertion(){

    // assert truth
        bytes32 claim;
        address asserter;
        address callbackRecipient;
        address escalationManager;
        uint64 liveness;
        address currency;
        uint256 bond;
        bytes32 identifier;
        bytes32 domainId;
        bytes32 assertionID;

    assertionID = assertTruth(
        claim,
        asserter,
        callbackRecipient,
        escalationManager,
        liveness,
        currency,
        bond,
        identifier,
        domainId
    );
    // assert that contract has enough balance to cover the bond of the just asserted truth
    uint256 contractBalanceAfter = tokenBalanceOf(currency, currentContract);
    
    assert contractBalanceAfter >= bond,"contract should atleast have enough balance the cover the aserted truth";
}

rule whochangedDisputer(method f){
    env e;
    bytes32 assertionID;
    address _disputer = getAssertionDisputer(assertionID);
    calldataarg args;
    f(e, args);
    address disputer_ = getAssertionDisputer(assertionID);
    assert _disputer == disputer_;
}



// A CVL copy implementation of the assertion fee calculation.
function assertionFee(uint256 bond) returns uint256 {
    return to_uint256((burnedBondPercentage()*bond)/(10^18));
}