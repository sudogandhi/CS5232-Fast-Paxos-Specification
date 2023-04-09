--------------------------- MODULE Paxos -----------------------------
(*
    Notes:
    1. Square brackets can be used to define a set of functions. [X -> Y]
    2. Curly brackets can be used to define a set of values. {x \in SUBSET X}
*)
EXTENDS TLC, Naturals, FiniteSets, Integers, Sequences

CONSTANTS any, none, Replicas, Values, Ballots, Quorums

VARIABLES messages \* Set of all messages sent.
VARIABLES decision \* Decided value of an acceptor.
VARIABLES maxBallot \* Maximum ballot an acceptor has seen.
VARIABLES maxVBallot \* Maximum ballot an acceptor has accepted.
VARIABLES maxValue \* Maximum value an acceptor has accepted.

vars == <<messages, decision, maxBallot, maxVBallot, maxValue>>

P1aMessage == [type : {"P1a"},
               ballot : Ballots \ {0}]
P1bMessage == [type : {"P1b"},
               ballot : Ballots,
               acceptor : Replicas,
               maxVBallot : Ballots,
               maxValue : Values \union {none}] \* (maxVBallot = 0) <=> (maxValue = none)
P2aMessage == [type : {"P2a"},
               ballot : Ballots,
               value : Values \union {any}]
P2bMessage == [type : {"P2b"},
               ballot : Ballots,
               acceptor : Replicas,
               value : Values]
Message == P1aMessage \union P1bMessage \union P2aMessage \union P2bMessage

PaxosAssume == /\ IsFiniteSet(Replicas)
               /\ any \notin Values \union {none}
               /\ none \notin Values \union {any}
               /\ Ballots \subseteq Nat /\ 0 \in Ballots
               /\ \A q \in Quorums : q \subseteq Replicas
               /\ \A q, r \in Quorums : q \intersect r # {}

ASSUME PaxosAssume

p1aMessages == {m \in messages : m.type = "P1a"} \* Set of all P1a messages sent.
p1bMessages == {m \in messages : m.type = "P1b"} \* Set of all P1b messages sent.
p2aMessages == {m \in messages : m.type = "P2a"} \* Set of all P2a messages sent.
p2bMessages == {m \in messages : m.type = "P2b"} \* Set of all P2b messages sent.

ForcedValue(M) == (CHOOSE m \in M : \A n \in M : n.maxVBallot <= m.maxVBallot).maxValue

SendMessage(m) == messages' = messages \union {m}

(*
    Phase 1a:

    A Proposer creates a message, which we call a "Prepare", identified with a ballot b.
    Note that b is not the value to be proposed and maybe agreed on, but just a number
    which uniquely identifies this initial message by the proposer (to be sent to the acceptors).

    The ballot b must be greater than any ballot used in any of the previous Prepare messages by this Proposer.
    But since the system is asynchronous, and messages may be delayed and arrive later, there is no need to explicitly
    model this.

    Then, it sends the Prepare message containing b to at least a Quorum of Acceptors.
    Note that the Prepare message only contains the ballot b (that is, it does not have to contain the proposed
    value).

    A Proposer should not initiate Paxos if it cannot communicate with at least a Quorum of Acceptors.
*)
PaxosPrepare ==
    /\ UNCHANGED<<decision, maxBallot, maxVBallot, maxValue>>
    /\ \E b \in Ballots \ {0} :
        SendMessage([type |-> "P1a",
                     ballot |-> b])

(*
    Phase 1b:

    Any of the Acceptors waits for a Prepare message from any of the Proposers.
    If an Acceptor receives a Prepare message, the Acceptor must look at the ballot b of the just received Prepare message.

    There are two cases:

        1. If b is higher than every previous proposal number received, from any of the Proposers, by the Acceptor,
           then the Acceptor must return a message, which we call a "Promise", to the Proposer, to ignore all future
           proposals having a ballot less than b. If the Acceptor accepted a proposal at some point in the past, it
           must include the previous proposal number, say u, and the corresponding accepted value, say w, in its response to the Proposer.

        2. Otherwise (that is, b is less than or equal to any previous proposal number received from any
           Proposer by the Acceptor) the Acceptor can ignore the received proposal.
           It does not have to answer in this case for Paxos to work.
*)
PaxosPromise ==
    /\ UNCHANGED<<decision, maxVBallot, maxValue>>
    /\ \E a \in Replicas, m \in p1aMessages :
        /\ maxBallot[a] < m.ballot
        /\ maxBallot' = [maxBallot EXCEPT ![a] = m.ballot]
        /\ SendMessage([type |-> "P1b",
                        ballot |-> m.ballot,
                        acceptor |-> a,
                        maxVBallot |-> maxVBallot[a],
                        maxValue |-> maxValue[a]])

(*
    Phase 2a:

    If a Proposer receives Promises from a Quorum of Acceptors, it needs to set a value v to its proposal.
    If any Acceptors had previously accepted any proposal, then they'll have sent their values to the Proposer,
    who now must set the value of its proposal, v, to the value associated with the highest proposal ballot reported by
    the Acceptors, let's call it z. If none of the Acceptors had accepted a proposal up to this point, then the Proposer
    may choose the value it originally wanted to propose, say x.

    The Proposer sends an Accept message, (b, v), to a Quorum of Acceptors with the chosen value for its proposal, v, and the ballot
    number b (which is the same as the number contained in the Prepare message previously sent to the Acceptors). So, the Accept message
    is either (b, v=z) or, in case none of the Acceptors previously accepted a value, (n, v=x).

    This Accept message should be interpreted as a "request", as in "Accept this proposal, please!". 
*)
PaxosAccept ==
    /\ UNCHANGED<<decision, maxBallot, maxVBallot, maxValue>>
    /\ \E b \in Ballots, q \in Quorums, v \in Values :
        /\ \A m \in p2aMessages : ~(m.ballot = b)
        /\ LET M == {m \in p1bMessages : m.ballot = b /\ m.acceptor \in q}
           IN /\ \A a \in q : \E m \in M : m.acceptor = a
              /\ \/ \A m \in M : m.maxValue = none
                 \/ v = ForcedValue(M)
              /\ SendMessage([type |-> "P2a",
                              ballot |-> b,
                              value |-> v])

(*
    Phase 2b:

    If an Acceptor receives an Accept message, (b, v), from a Proposer, it must accept it if and only if it has not already
    promised (in Phase 1b of the Paxos protocol) to only consider proposals having a ballot greater than b.

    If the Acceptor has not already promised (in Phase 1b) to only consider proposals having a ballot greater than b,
    it should register the value v (of the just received Accept message) as the accepted value (of the Protocol), and send
    an Accepted message to the Proposer and every Acceptor.

    Else, it can ignore the Accept message or request.
*)
PaxosAccepted ==
    /\ UNCHANGED<<decision>>
    /\ \E a \in Replicas, m \in p2aMessages :
        /\ m.value \in Values
        /\ maxBallot[a] <= m.ballot
        /\ maxBallot' = [maxBallot EXCEPT ![a] = m.ballot]
        /\ maxVBallot' = [maxVBallot EXCEPT ![a] = m.ballot]
        /\ maxValue' = [maxValue EXCEPT ![a] = m.value]
        /\ SendMessage([type |-> "P2b",
                        ballot |-> m.ballot,
                        acceptor |-> a,
                        value |-> m.value])

(*
    Consensus is achieved when a majority of Acceptors accept the same ballot (rather than the same value).
    Because each ballot is unique to a Proposer and only one value may be proposed per ballot, all Acceptors
    that accept the same ballot thereby accept the same value.

    These facts result in a few counter-intuitive scenarios that do not impact correctness:

        1. Acceptors can accept multiple values, a value may achieve a majority across Acceptors (with different ballots) only to later be changed.
        2. Acceptors may continue to accept proposals after an identifier has achieved a majority.
        3. However, the Paxos protocol guarantees that consensus is permanent and the chosen value is immutable. 
*)
PaxosDecide ==
    /\ UNCHANGED<<messages, maxBallot, maxVBallot, maxValue>>
    /\ \E b \in Ballots, q \in Quorums :
        LET M == {m \in p2bMessages : m.ballot = b /\ m.acceptor \in q}
        IN /\ \A a \in q : \E m \in M : m.acceptor = a
           /\ \E m \in M : decision' = m.value

\* Success is achieved when all replicas reach a consensus.
PaxosSuccess ==
    /\ UNCHANGED<<messages, decision, maxBallot, maxVBallot, maxValue>>
    /\ decision \in Values
    /\ Print(Append("Success! Value: ", ToString(decision)), TRUE)

PaxosInit == /\ messages = {}
             /\ decision = none
             /\ maxBallot = [r \in Replicas |-> 0]
             /\ maxVBallot = [r \in Replicas |-> 0]
             /\ maxValue = [r \in Replicas |-> none]

PaxosNext == \/ PaxosPrepare
             \/ PaxosPromise
             \/ PaxosAccept
             \/ PaxosAccepted
             \/ PaxosDecide
             \/ PaxosSuccess

PaxosSpec == PaxosInit /\ [][PaxosNext]_vars /\ SF_vars(PaxosSuccess)

PaxosTypeOK == /\ messages \subseteq Message
               /\ decision \in Values \union {none}
               /\ maxBallot \in [Replicas -> Ballots]
               /\ maxVBallot \in [Replicas -> Ballots]
               /\ maxValue \in [Replicas -> Values \union {none}]

\* Only proposed values can be learned.
PaxosNontriviality ==
    /\ \/ decision = none
       \/ \E m \in p2aMessages : m.value = decision
    /\ \A m \in p1bMessages : /\ m.maxValue \in Values \/ 0 = m.maxVBallot
                              /\ m.maxValue = none \/ 0 < m.maxVBallot

\* At most 1 value can be learned.
PaxosConsistency == decision = none \/ decision = decision'

PaxosSafetyProperty == [][PaxosNontriviality]_vars /\ [][PaxosConsistency]_vars

PaxosSymmetry == Permutations(Values) \union Permutations(Replicas)

===============================================================