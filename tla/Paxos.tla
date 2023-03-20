--------------------------- MODULE Paxos -----------------------------
(*
    Syntax Notes:
    - Square brackets can be used to define a set of functions. [X -> Y]
    - Curly brackets can be used to define a set of values. {x \in SUBSET X}
*)
EXTENDS TLC, Naturals, FiniteSets, Integers

CONSTANTS Replicas
CONSTANTS None, Values
CONSTANTS Ballots

VARIABLES messages \* Set of all messages sent.
VARIABLES decision \* Decided value of the replicas.

AnyValue == CHOOSE v \in Values : TRUE

PaxosQuorums == {q \in SUBSET Replicas : (Cardinality(Replicas) \div 2) < Cardinality(q)}

P1aMessage == [type : {"P1a"},
               ballot : Ballots,                       \* Ballot is in set Ballot.
               proposer : Replicas]                    \* Proposer is in set Replicas.

P1bMessage == [type : {"P1b"},
               ballot : Ballots,                       \* Ballot is in set Ballot.
               proposer : Replicas,                    \* Proposer is in set Replicas.
               acceptor : Replicas,                    \* Acceptor is in set Replicas.
               maxBallot : Ballots \union {None},      \* Max ballot is a member of set Ballots or is None.
               maxValue : Values \union {None}]        \* Max value is a member of set Values or is None.
                                                       \* (Max Ballot = None) <=> (Max Value = None)

P2aMessage == [type : {"P2a"},
               ballot : Ballots,                       \* Ballot value is in set Ballot.
               proposer : Replicas,                    \* Proposer is in set Replicas.
               value : Values]                         \* Value is in set Values.

P2bMessage == [type : {"P2b"},
               ballot : Ballots,                       \* Ballot is in set Ballot.
               proposer : Replicas,                    \* Proposer is in set Replicas.
               acceptor : Replicas,                    \* Acceptor is in set Replicas.
               value : Values]                         \* Value is in set Values.
               
P3Message == [type : {"P3"},
              ballot : Ballots,                        \* Ballot value is in set Ballot.
              value : Values]                          \* Value is in set Values.

\* Message is the union of P1aMessage, P1bMessage, P2aMessage, P2bMessage and P3Message.
Message == P1aMessage \union P1bMessage \union P2aMessage \union P2bMessage \union P3Message

(*
    For every quorum we compute from PaxosQuorums, we assume that
        1) it is a subset of set Replicas and
        2) intersection of two quorums should not be as empty set,
        3) therefore there must be at least one common element between any two quorums.
*)
QuorumAssume == /\ \A q \in PaxosQuorums : q \subseteq Replicas
                /\ \A q, r \in PaxosQuorums : q \intersect r # {}

(*
    We assume that the set Ballots is a subset of natural numbers,
    and 0 is also part of Ballots
*)
BallotAssume == /\ Ballots \subseteq Nat
                /\ 0 \in Ballots

ASSUME QuorumAssume /\ BallotAssume

Filter(M, f(_)) == {m \in M : f(m)}

\* Filter all the messages in M with proposer as p.
FilterProposer(M, p) == Filter(M, LAMBDA m : m.proposer = p)

\* Filter all the messages in M with acceptor as a.
FilterAcceptor(M, a) == Filter(M, LAMBDA m : m.acceptor = a)

\* Filter all the messages in M with ballot number as b.
FilterBallot(M, b) == Filter(M, LAMBDA m : m.ballot = b)

\* Filter all the messages in M for which the maxBallot and maxValue is not None.
FilterMax(M) == Filter(M, LAMBDA m : m.maxBallot # None /\ m.maxValue # None)

p1aMessages == Filter(messages, LAMBDA m : m.type = "P1a") \* Set of all P1a messages sent.
p1bMessages == Filter(messages, LAMBDA m : m.type = "P1b") \* Set of all P1b messages sent.
p2aMessages == Filter(messages, LAMBDA m : m.type = "P2a") \* Set of all P2a messages sent.
p2bMessages == Filter(messages, LAMBDA m : m.type = "P2b") \* Set of all P2b messages sent.
p3Messages == Filter(messages, LAMBDA m : m.type = "P3") \* Set of all P3 messages sent.

MaxMessage(M) == CHOOSE m \in M : \A n \in M : n = m \/ n.ballot < m.ballot

\* Filter all the messages which acceptor as a and storing that in M.
\* Get the ballot for the message which has the largest ballot number in M.
\* If M is empty then return None.
MaxBallot(a) == LET M == FilterAcceptor(p2bMessages, a)
                IN IF M = {} THEN None ELSE MaxMessage(M).ballot

\* Filter all the messages which acceptor as a and storing that in M.
\* Get the value for the message which has the largest ballot number in M.
\* If M is empty then return None.
MaxValue(a) == LET M == FilterAcceptor(p2bMessages, a)
               IN IF M = {} THEN None ELSE MaxMessage(M).value

SelectMaxMessage(M) == CHOOSE m \in M : \A n \in M : n = m \/ n.ballot <= m.ballot

SelectMaxValue(M) == SelectMaxMessage(FilterMax(M)).maxValue

SendMessage(m) == messages' = messages \union {m}

DecideValue(a, v) == decision' = [decision EXCEPT ![a] = v]

\* Phase 1a
PaxosPrepare ==
    \* A proposer, chooses a ballot number greater than any used so far, and sends a P1a message.
    /\ UNCHANGED<<decision>>
    /\ \E b \in Ballots, p \in Replicas :
        /\ \A m \in FilterProposer(p1aMessages, p) : m.ballot < b
        /\ SendMessage([type |-> "P1a",
                        ballot |-> b,
                        proposer |-> p])

\* Phase 1b
PaxosPromise ==
    \* If an acceptor receives a P1a message,
    \* with a ballot number larger than any P1a or P2a ballot it has seen before, it replies with a P1b message.
    \* If it has already accepted a value from a smaller ballot previously, send the value and ballot to the proposer.
    /\ UNCHANGED<<decision>>
    /\ \E m \in p1aMessages, a \in Replicas :
        /\ \A n \in FilterAcceptor(p1bMessages \union p2bMessages, a) : n.ballot < m.ballot
        /\ SendMessage([type |-> "P1b",
                        ballot |-> m.ballot,
                        proposer |-> m.proposer,
                        acceptor |-> a,
                        maxBallot |-> MaxBallot(a),
                        maxValue |-> MaxValue(a)])

\* Phase 2a
PaxosAccept ==
    \* Free case:
    \* If a proposer p sends a P1a message with ballot b,
    \* and receives a quorum q of P1b replies,
    \* where all replies have no accepted value or accepted ballot,
    \* send a P2a message with any value.
    \/ /\ UNCHANGED<<decision>>
       /\ \E p \in Replicas, b \in Ballots, q \in PaxosQuorums :
              LET M == FilterBallot(FilterProposer(p1bMessages, p), b)        \* filtering all the messages sent by proposer p with ballot b
              IN /\ \A a \in q : FilterAcceptor(M, a) # {}                    \* checking for a quorum of acceptors who sent P1b replies.
                 /\ \A m \in M : m.maxValue = None /\ m.maxBallot = None      \* checking for all the messages in M, there should be no accepted value.
                 /\ SendMessage([type |-> "P2a",
                                 ballot |-> b,
                                 proposer |-> p,
                                 value |-> AnyValue])
    \* Forced case:
    \* If a proposer p sends a P1a message with ballot b,
    \* and receives a quorum q of P1b replies,
    \* where there exists a reply with an accepted value and accepted ballot,
    \* send a P2a message with the value of the highest accepted ballot.
    \/ /\ UNCHANGED<<decision>>
       /\ \E p \in Replicas, b \in Ballots, q \in PaxosQuorums :
              LET M == FilterBallot(FilterProposer(p1bMessages, p), b)        \* filtering all the messages sent by proposer p with ballot b
              IN /\ \A a \in q : FilterAcceptor(M, a) # {}                    \* checking for a quorum of acceptors who sent P1b replies.
                 /\ \E m \in M : m.maxValue # None /\ m.maxBallot # None      \* checking for all the messages in M, there should not be any message with no accepted value.
                 /\ SendMessage([type |-> "P2a",
                                 ballot |-> b,
                                 proposer |-> p,
                                 value |-> SelectMaxValue(M)])

\* Phase 2b
PaxosAccepted ==
    \* If an acceptor a receives a P2a message,
    \* with a ballot number greater or equal to any P1a or P2a messages it has received so far,
    \* it accepts the new value and ballot number,
    \* and sends a P2b message.
    /\ UNCHANGED<<decision>>
    /\ \E m \in p2aMessages, a \in Replicas :
        LET M == FilterAcceptor(p1bMessages \union p2bMessages , a)
        IN /\ \A n \in M : n.ballot <= m.ballot
           /\ SendMessage([type |-> "P2b",
                           ballot |-> m.ballot,
                           proposer |-> m.proposer,
                           acceptor |-> a,
                           value |-> m.value])

\* Phase 3
PaxosDecide ==
    \* If a proposer receives a quorum of P2b messages for a ballot,
    \* it sends a P3 message with that ballot and value.
    /\ UNCHANGED<<decision>>
    /\ \E p \in Replicas, b \in Ballots, v \in Values, q \in PaxosQuorums :
           /\ \A a \in q : LET M == FilterAcceptor(FilterProposer(p2bMessages, p), a)
                           IN \E m \in M : m.ballot = b /\ m.value = v
           /\ SendMessage([type |-> "P3",
                           ballot |-> b,
                           value |-> v])

PaxosDecided ==
    /\ UNCHANGED<<messages>>
    /\ \E msg \in p3Messages, a \in Replicas : DecideValue(a,msg.value)

PaxosEnd ==
    /\ UNCHANGED<<messages, decision>>
    /\ \A a, b \in Replicas : decision[a] = decision[b] /\ decision[a] # None

PaxosInit == /\ messages = {}
             /\ decision = [r \in Replicas |-> None]

PaxosNext == \/ PaxosPrepare
             \/ PaxosPromise
             \/ PaxosAccept
             \/ PaxosAccepted
             \/ PaxosDecide
             \/ PaxosDecided
             \/ PaxosEnd

PaxosSpec == PaxosInit /\ [][PaxosNext]_<<decision, messages>> /\ WF_<<decision, messages>>(PaxosEnd)

PaxosTypeOK == /\ None \notin Values
               /\ messages \subseteq Message
               /\ decision \in [Replicas -> Values \union {None}]

DecideConflict ==
    \E a, b \in Replicas : /\ decision[a] # None /\ decision[b] # None
                           /\ decision[a] # decision[b]

DecideChange ==
    \E a \in Replicas : /\ decision[a] # None
                        /\ decision[a] # decision'[a]

InvalidMax ==
    \E m \in p1bMessages : \/ m.maxValue = None /\ m.maxBallot # None
                           \/ m.maxValue # None /\ m.maxBallot = None

InvalidDecide ==
    \E a \in Replicas : /\ decision[a] # None
                        /\ decision[a] # MaxMessage(p2aMessages).value

PaxosSafetyProperty == /\ [][~DecideChange]_<<messages, decision>>
                       /\ [][~DecideConflict]_<<messages, decision>>
                       /\ [][~InvalidMax]_<<messages, decision>>
                       /\ [][~InvalidDecide]_<<messages, decision>>

PaxosLivenessProperty == TRUE

PaxosSymmetry == Permutations(Values) \union Permutations(Replicas)

===============================================================