if [[ "$1" ]]
then
    RULE="--rule $1"
fi

if [[ "$2" ]]
then
    MSG="- $2"
fi
certoraRun ./certora/optimistic-asserter/harness/OptimisticAsserter.sol:OptimisticAsserterHarness \
            ./certora/optimistic-asserter/harness/MockEscalationManager.sol \
            ./certora/optimistic-asserter/harness/MockStore.sol:Store \
           ./contracts/data-verification-mechanism/implementation/Finder.sol \
           ./contracts/data-verification-mechanism/implementation/IdentifierWhitelist.sol \
           ./contracts/common/implementation/AddressWhitelist.sol \
           ./contracts/common/implementation/TestnetERC20.sol \
           ./contracts/common/test/BasicERC20.sol \
\
\
--verify OptimisticAsserterHarness:certora/optimistic-asserter/specs/Asserter_Bonds.spec \
\
\
--link OptimisticAsserterHarness:finder=Finder \
\
\
--packages @openzeppelin=../../node_modules/@openzeppelin \
--path ./ \
--solc solc8.16 \
--send_only \
--settings -byteMapHashingPrecision=11,-mediumTimeout=200 \
--loop_iter 3 \
--staging master \
--optimistic_loop \
$RULE \
    --msg "UMA Asserter Bonds spec: $RULE $MSG"

# ./contracts/data-verification-mechanism/implementation/Store.sol \
# --typecheck_only \
