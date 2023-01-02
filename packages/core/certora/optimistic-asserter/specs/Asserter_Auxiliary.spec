// For every new spec you create, import this basic spec file:
import "./Asserter_Base.spec"
import "./dispatchedMethods.spec"

/*************************************************
*                Custom rules                    *
**************************************************/
// If calling 'assertTruth' twice, it cannot yield the same assertion ID.
rule cannotAssertTruthTwiceForSameID() {
    env e1;
    env e2;
    calldataarg args1; 
    calldataarg args2;
    bytes32 ID1 = assertTruth(e1, args1);
    bytes32 ID2 = assertTruth(e2, args2);

    // It's enough to check this rule for a single instance of the currency
    // One can try to test this rule without these requirements.
    require getAssertionCurrency(ID1) == testERC20;
    require getAssertionCurrency(ID2) == testERC20;
    assert ID1 != ID2;
}

// This rule makes sure that if we can call assertTruth with some parameters 
// (without reverting), then we can call it again with the same parameters but
// just changing the liveness.

// Violated since ID2 can lead to failure of 
// require(!assertionPolicy.blockAssertion, "Assertion not allowed") as a part of 
// the assertion policy, as it depends on the assertionID of each assertion.
rule assertTruthSucceedsForEveryLiveness(uint64 liveness1, uint64 liveness2) 
{    
    env e;
    bytes claim;
    address asserter;
    address callbackRecipient;
    address escalationManager;
    address currency = testERC20;
    uint256 bond;
    bytes32 identifier;
    bytes32 domainId;

    // Testing two different liveness parameters.
    require liveness1 != liveness2;
    // Make sure we don't overflow.
    require liveness2 + e.block.timestamp <= max_uint64;

    // Assuming no previous call to assertTruth was made:
    bytes32 ID2 = getId(e,claim,callbackRecipient,escalationManager,liveness2,currency,bond,identifier);
    require getAssertionAsserter(ID2) == 0;
    storage initState = lastStorage;
    
    // Here we "force" the combination of parameters to succeed.
    assertTruth(e,claim,asserter,callbackRecipient,escalationManager,
        liveness1,currency,bond,identifier,domainId);

    // Call again, with a different liveness parameter, at the initial storage state.
    mayEnter() at initState;

    assertTruth@withrevert(e,claim,asserter,callbackRecipient,escalationManager,
        liveness2,currency,bond,identifier,domainId);

    assert !lastReverted;
}

// Calling assertTruth by a user should never front-run (DOS attack) 
// another user who wishes to call assertTruth
rule assertTruthFrontRunning() {
    env e1; env e2;
    require e1.msg.sender != currentContract;
    require e2.msg.sender != currentContract;
    require e1.msg.sender != e2.msg.sender;
    storage initState = lastStorage;

    bytes claim1; bytes claim2;
    // Assuming one word length for claims
    require claim1.length == 32;
    require claim2.length == 32;

    address asserter1; address asserter2;
    address callbackRecipient1; address callbackRecipient2;
    address escalationManager1; address escalationManager2;
    uint64 liveness1; uint64 liveness2;
    address currency1 = testERC20; address currency2 = testERC20;
    uint256 bond1; uint256 bond2;
    bytes32 identifier1; bytes32 identifier2;
    bytes32 domainId1; bytes32 domainId2;

    // Calling assertTruth by e1.msg.sender successfully.
    bytes32 assertionId1 = assertTruth(e1,claim1,asserter1,callbackRecipient1,escalationManager1,
        liveness1,currency1,bond1,identifier1,domainId1);

    // Starting from the initial storage state, we call assertTruth by a
    // different user e2.msg.sender.
    bytes32 assertionId2 = assertTruth(e2,claim2,asserter2,callbackRecipient2,escalationManager2,
        liveness2,currency2,bond2,identifier2,domainId2) at initState;

    // Simply checking that the assertion ids should be different
    assert assertionId2 != assertionId1;

    // Now making sure that the original user can call the same function without reverting.
    assertTruth@withrevert(e1,claim1,asserter1,callbackRecipient1,escalationManager1,
        liveness1,currency1,bond1,identifier1,domainId1);

    assert !lastReverted;
}

// Verified for the setting -byteMapHashingPrecision > 10
rule getIDInjectivity() {
    env e1; env e2;
    require e1.msg.sender != e2.msg.sender;

    bytes claim1; bytes claim2;
    // Assuming one word length for claims
    require claim1.length == 32;
    require claim2.length == 32;
    
    address callbackRecipient1; address callbackRecipient2;
    address escalationManager1; address escalationManager2;
    uint64 liveness1; uint64 liveness2;
    address currency1; address currency2;
    uint256 bond1; uint256 bond2;
    bytes32 identifier1; bytes32 identifier2;

    bytes32 ID1 = getId(e1, claim1, callbackRecipient1,
        escalationManager1, liveness1, currency1, bond1, identifier1);

    bytes32 ID2 = getId(e2, claim2, callbackRecipient2, 
        escalationManager2, liveness2, currency2, bond2, identifier2);

    assert ID1 != ID2;
}

// Verified
rule onlyOneAssertionAtATime(method f, bytes32 assertion, bytes32 other) 
filtered{f -> !f.isView && !isMultiCall(f)} {
    env e;
    calldataarg args;
    // We distinguish between some assertion and 'another' one.
    require other != assertion;

    bool settled_before = getAssertionSettled(assertion);
    bool settledOther_before = getAssertionSettled(other);
    bool resolution_before = getAssertionSettlementResolution(assertion);
    bool resolutionOther_before = getAssertionSettlementResolution(other);
        f(e, args);
    bool settled_after = getAssertionSettled(assertion);
    bool settledOther_after = getAssertionSettled(other);
    bool resolution_after = getAssertionSettlementResolution(assertion);
    bool resolutionOther_after = getAssertionSettlementResolution(other);

    // If some assertion parameter was changed after calling a method,
    // we expect that these parameters must not change for any other assertion.
    assert (settled_before != settled_after || resolution_before != resolution_after)
        =>
        (settledOther_before == settledOther_after && resolutionOther_before == resolutionOther_after);
}
