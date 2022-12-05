certoraRun ./certora/harness/OptimisticAsserter.sol:OptimisticAsserterHarness \
            ./certora/harness/MockEscalationManager.sol \
           ./contracts/data-verification-mechanism/implementation/Finder.sol \
           ./contracts/data-verification-mechanism/implementation/IdentifierWhitelist.sol \
           ./contracts/data-verification-mechanism/implementation/Store.sol \
           ./contracts/common/implementation/AddressWhitelist.sol \
           ./contracts/common/implementation/TestnetERC20.sol \
           ./contracts/common/test/BasicERC20.sol \
\
\
--verify OptimisticAsserterHarness:certora/specs/Asserter_Auxiliary.spec \
\
\
--link OptimisticAsserterHarness:finder=Finder \
\
\
--packages @openzeppelin=../../node_modules/@openzeppelin \
--path . \
--solc solc8.16 \
--send_only \
--staging \
--rule whoChanged_assertionBond \
--settings -mediumTimeout=50 \
--loop_iter 2 \
--optimistic_loop \
--msg "UMA Asserter : whoChanged_assertionBond"
