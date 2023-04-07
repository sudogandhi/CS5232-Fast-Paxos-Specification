--------------------------- MODULE FastPaxos2 -----------------------------
EXTENDS TLC, Naturals, FiniteSets, Integers

INSTANCE Paxos

CONSTANTS Replicas, Coordinator
CONSTANTS None, Any, Values
CONSTANTS Ballots, Quorums, FastQuorums

VARIABLES messages \* Set of all messages sent.
VARIABLES decision \* Value an acceptor has decided.
VARIABLES maxBallot \* Maximum ballot an acceptor has seen.
VARIABLES maxVBallot \* Maximum ballot an acceptor has accepted.
VARIABLES maxValue \* Maximum value an acceptor has accepted.
VARIABLES mode
VARIABLES maxCBallot

ASSUME /\ Coordinator \in Replicas
       /\ \A q \in FastQuorums : q \subseteq Replicas
       /\ \A q, r \in FastQuorums : q \intersect r # {}
       /\ \A q \in Quorums : \A r, s \in FastQuorums : q \intersect r \intersect s # {}

\* Fast Phase 2a (Any)
FastAcceptAny ==
    /\ UNCHANGED<<decision, maxBallot, maxVBallot, maxValue>>
    /\ mode = "Fast"
    /\ \E b \in Ballots :
        /\ maxCBallot < b
        /\ maxCBallot' = b
        /\ SendMessage([type |-> "P2a",
                        ballot |-> b,
                        proposer |-> Coordinator,
                        value |-> Any])

\* Phase 2a
FastAccept == TRUE

\* Phase 2b (Any)
FastAcceptedAny ==
    /\ UNCHANGED<<decision>>
    /\ \E m \in p2aMessages, a \in Replicas, v \in Values :
        /\ m.value = Any
        /\ maxBallot[a] <= m.ballot
        /\ maxBallot' = [maxBallot EXCEPT ![a] = m.ballot]
        /\ maxVBallot' = [maxVBallot EXCEPT ![a] = m.ballot]
        /\ maxValue' = [maxValue EXCEPT ![a] = v]
        /\ \A n \in p2bMessages : ~(n.ballot = b /\ n.proposer = m.proposer /\ n.acceptor = a)
        /\ SendMessage([type |-> "P2b",
                        ballot |-> m.ballot,
                        proposer |-> m.proposer,
                        acceptor |-> a,
                        value |-> v])

\* Invariant for all the variables declared.
FastTypeOK == /\ PaxosTypeOK
              /\ Coordinator \in Replicas
              /\ mode \in {"Fast", "Classic"}
              /\ maxCBallot \in Ballots

FastInit == /\ PaxosInit
            /\ coordBallot = 0
            /\ mode = "Fast"

FastNext == TRUE

FastSpec == /\ FastPaxosInit

===============================================================