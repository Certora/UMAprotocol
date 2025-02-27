// SPDX-License-Identifier: AGPL-3.0-only
pragma solidity 0.8.16;

import "../VotingV2.sol";
import "../../../common/implementation/Testable.sol";

// Test contract used to manage the time for the contract in tests.
contract VotingV2ControllableTiming is VotingV2, Testable {
    constructor(
        uint256 _emissionRate,
        uint256 _spamDeletionProposalBond,
        uint64 _unstakeCoolDown,
        uint64 _phaseLength,
        uint64 _minRollToNextRoundLength,
        uint256 _gat,
        uint64 _startingRequestIndex,
        address _votingToken,
        address _finder,
        address _slashingLibrary,
        address _previousVotingContract,
        address _timerAddress
    )
        VotingV2(
            _emissionRate,
            _spamDeletionProposalBond,
            _unstakeCoolDown,
            _phaseLength,
            _minRollToNextRoundLength,
            _gat,
            _startingRequestIndex,
            _votingToken,
            _finder,
            _slashingLibrary,
            _previousVotingContract
        )
        Testable(_timerAddress)
    {}

    function getCurrentTime() public view override(Staker, Testable) returns (uint256) {
        return Testable.getCurrentTime();
    }

    function commitVote(
        bytes32 identifier,
        uint256 time,
        bytes32 hash
    ) external virtual onlyIfNotMigrated() {
        commitVote(identifier, time, "", hash);
    }

    function revealVote(
        bytes32 identifier,
        uint256 time,
        int256 price,
        int256 salt
    ) external virtual {
        revealVote(identifier, time, price, "", salt);
    }

    function commitAndEmitEncryptedVote(
        bytes32 identifier,
        uint256 time,
        bytes32 hash,
        bytes memory encryptedVote
    ) public {
        commitAndEmitEncryptedVote(identifier, time, "", hash, encryptedVote);
    }

    function getPendingPriceRequestsArray() external view returns (bytes32[] memory) {
        return pendingPriceRequests;
    }

    function getPriceRequestStatuses(PendingRequest[] memory requests) external view returns (RequestState[] memory) {
        PendingRequestAncillary[] memory requestsAncillary = new PendingRequestAncillary[](requests.length);

        for (uint256 i = 0; i < requests.length; i = unsafe_inc(i)) {
            requestsAncillary[i].identifier = requests[i].identifier;
            requestsAncillary[i].time = requests[i].time;
            requestsAncillary[i].ancillaryData = "";
        }
        return getPriceRequestStatuses(requestsAncillary);
    }
}

// Test contract used to access internal variables in the Voting contract.
contract VotingV2Test is VotingV2ControllableTiming {
    constructor(
        uint256 _emissionRate,
        uint256 _spamDeletionProposalBond,
        uint64 _unstakeCoolDown,
        uint64 _phaseLength,
        uint64 _minRollToNextRoundLength,
        uint256 _gat,
        uint64 _startingRequestIndex,
        address _votingToken,
        address _finder,
        address _slashingLibrary,
        address _previousVotingContract,
        address _timerAddress
    )
        VotingV2ControllableTiming(
            _emissionRate,
            _spamDeletionProposalBond,
            _unstakeCoolDown,
            _phaseLength,
            _minRollToNextRoundLength,
            _gat,
            _startingRequestIndex,
            _votingToken,
            _finder,
            _slashingLibrary,
            _previousVotingContract,
            _timerAddress
        )
    {}
}
