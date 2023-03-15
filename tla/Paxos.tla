--------------------------- MODULE Paxos -----------------------------
(*
    Notes:
    - Square brackets can be used to define a set of functions. [X -> Y]
    - Curly brackets can be used to define a set of values. {x \in SUBSET X}
*)
EXTENDS TLC, Naturals, FiniteSets, Integers

CONSTANTS Replicas
CONSTANTS None, Values
CONSTANTS Ballots

VARIABLES messages \* The set of all messages sent.
VARIABLES decision \* The decided value of the replicas.

AnyValue == CHOOSE v \in Values : TRUE

PaxosQuorums == {q \in SUBSET Replicas : (Cardinality(Replicas) \div 2) < Cardinality(q)}

P1aMessage == [type : {"P1a"},
               ballot : Ballots,                            \* ballot value belongs to set Ballot.
               proposer : Replicas]                         \* proposer has to be a part of set Replicas

P1bMessage == [type : {"P1b"},
               ballot : Ballots,
               proposer : Replicas,                         \* proposer has to be a part of set Replicas
               acceptor : Replicas,                         \* acceptor has to be a part of set Replicas
               acceptedBallot : Ballots \union {None},      \* either the accepted ballot is a member of set Ballots or is None.
               acceptedValue : Values \union {None}]        \* either the accepted value is a member of set Values or is None.
                                                            \* (acceptedBallot=None) => (acceptedValue=None)
P2aMessage == [type : {"P2a"},
               ballot : Ballots,                            \* ballot value belongs to set Ballot.
               proposer : Replicas,                         \* proposer has to be a part of set Replicas
               value : Values]                              \* value has to be a part of set Values.

P2bMessage == [type : {"P2b"},
               ballot : Ballots,                            \* ballot value belongs to set Ballot.
               proposer : Replicas,                         \* proposer has to be a part of set Replicas
               acceptor : Replicas,                         \* acceptor has to be a part of set Replicas
               value : Values]                              \* value has to be a part of set Values.
               
P3Message == [type : {"P3"},
              ballot : Ballots,                            \* ballot value belongs to set Ballot.
              value : Values]                              \* value has to be a part of set Values.

\* Message will be a union of all five types of messages described so far.
Message == P1aMessage \union P1bMessage \union P2aMessage \union P2bMessage \union P3Message

(*
    For every quorum we compute from PaxosQuorums, we assume that
    1 - it is a subset of set Replicas
    2 - intersection of two quorums should not be as empty set,
    i.e. there must be atleast one common element between any two quorums.
*)
QuorumAssume == /\ \A q \in PaxosQuorums : q \subseteq Replicas
                /\ \A q, r \in PaxosQuorums : q \intersect r # {}

(*
    We assume that the set Ballots is a subset of natural numbers
    and 0 is also part of Ballots
*)
BallotAssume == /\ Ballots \subseteq Nat
                /\ 0 \in Ballots

ASSUME /\ QuorumAssume /\ BallotAssume


Filter(M, f(_)) == {m \in M : f(m)}

\* filter all the messages with proposer as p.
FilterProposer(M, p) == Filter(M, LAMBDA m : m.proposer = p)

\* filter all the messages with acceptor as a.
FilterAcceptor(M, a) == Filter(M, LAMBDA m : m.acceptor = a)

\* filter all the messages with ballot number as b.
FilterBallot(M, b) == Filter(M, LAMBDA m : m.ballot = b)

\* filter all the messages on the basis of type t. {"P1a","P1b","P2a","P2b"}
FilterType(M, t) == Filter(M, LAMBDA m : m.type = t)

\* filter all the messages for which the acceptor is present in the quorum q.
FilterQuorum(M, q) == Filter(M, LAMBDA m : m.acceptor \in q)

\* filter all the messages for which the acceptedBallot and acceptedValue is not None.
FilterAccepted(M) == Filter(M, LAMBDA m : m.acceptedBallot # None /\ m.acceptedValue # None)

P1aMessages == FilterType(messages, "P1a")
P1bMessages == FilterType(messages, "P1b")
P2aMessages == FilterType(messages, "P2a")
P2bMessages == FilterType(messages, "P2b")
P3Messages == FilterType(messages, "P3")


HasLargestBallot(M, m) == \A n \in M : n.ballot <= m.ballot

LargestBallotMessage(M) == CHOOSE m \in M : HasLargestBallot(M, m)

AcceptedBallot(a) == LET M == FilterAcceptor(P2bMessages, a)                            \* Filter all the messages which acceptor as a and storing that in M.
                     IN IF M = {} THEN None ELSE LargestBallotMessage(M).ballot         \* Get the ballot for the message which has the largest ballot number in M.
                                                                                        \* If M is empty then return None.


AcceptedValue(a) == LET M == FilterAcceptor(P2bMessages, a)                             \* Filter all the messages which acceptor as a and storing that in M.
                    IN IF M = {} THEN None ELSE LargestBallotMessage(M).value           \* Get the value for the message which has the largest ballot number in M.
                                                                                        \* If M is empty then return None.

SelectAcceptedValue(M) == (CHOOSE m \in M : (\A n \in M : n.ballot <= m.ballot)).value

SendMessage(m) == messages' = messages \union {m}

DecideValue(a, v) == decision' = [decision EXCEPT ![a] = v]

\* Phase 1a
PaxosPrepare ==
    \* A proposer sends a P1a message.
    \E b \in Ballots, p \in Replicas :
        /\ \A m \in FilterProposer(P1aMessages, p) : b > m.ballot
        /\ SendMessage([type |-> "P1a", ballot |-> b, proposer |-> p])
        /\ UNCHANGED<<decision>>

\* Phase 1b
PaxosPromise ==
    \* If an acceptor receives a P1a message,
    \* with a ballot number larger than any P1a or P2a ballot it has seen before,
    \* then it replies with a P1b message.
    \E m \in P1aMessages, a \in Replicas :
        /\ HasLargestBallot(FilterAcceptor(P1bMessages, a) \union
                            FilterAcceptor(P2bMessages, a), m)
        /\ SendMessage([type |-> "P1b",
                        ballot |-> m.ballot,
                        proposer |-> m.proposer,
                        acceptor |-> a,
                        acceptedBallot |-> AcceptedBallot(a),
                        acceptedValue |-> AcceptedValue(a)])
        /\ UNCHANGED<<decision>>

\* Phase 2a
PaxosAccept ==
    \* Free case:
    \* If a proposer p sends a P1a message with ballot b,
    \* and receives a quorum q of P1b replies,
    \* where all replies have no accepted value or accepted ballot,
    \* send a P2a message with any value.
    \/ /\ \E p \in Replicas, b \in Ballots, q \in PaxosQuorums:
              LET M == FilterBallot(FilterProposer(P1bMessages, p), b)                  \* filtering all the messages sent by proposer p with ballot b
              IN /\ \A a \in q : FilterAcceptor(M, a) # {}                              \* checking for a quorum of acceptors who sent P1b replies.
                 /\ \A m \in M : m.acceptedValue = None /\ m.acceptedBallot = None      \* checking for all the messages in M, there should be no accepted value.
                 /\ SendMessage([type |-> "P2a",
                                 ballot |-> b,
                                 proposer |-> p,
                                 value |-> AnyValue])
       /\ UNCHANGED<<decision>>
    \* Forced case:
    \* If a proposer p sends a P1a message with ballot b,
    \* and receives a quorum q of P1b replies,
    \* where there exists a reply with an accepted value and accepted ballot,
    \* send a P2a message with the value of the highest accepted ballot.
    \/ /\ \E p \in Replicas, b \in Ballots, q \in PaxosQuorums:
              LET M == FilterBallot(FilterProposer(P1bMessages, p), b)                  \* filtering all the messages sent by proposer p with ballot b
              IN /\ \A a \in q : FilterAcceptor(M, a) # {}                              \* checking for a quorum of acceptors who sent P1b replies.
                 /\ \E m \in M : m.acceptedValue # None /\ m.acceptedBallot # None      \* checking for all the messages in M, there should not be any message with no accepted value.
                 /\ SendMessage([type |-> "P2a",
                                 ballot |-> b,
                                 proposer |-> p,
                                 value |-> SelectAcceptedValue(FilterAccepted(M))])
       /\ UNCHANGED<<decision>>

\* Phase 2b
PaxosAccepted == /\ \E m \in P2aMessages, a \in Replicas: 
                    LET M == FilterAcceptor(P1bMessages \union  P2bMessages , a)
                    IN /\ \A n \in M : n.ballot <= m.ballot
                       /\ SendMessage([
                        type |-> "P2b",
                        ballot |-> m.ballot,
                        proposer |-> m.proposer,
                        acceptor |-> a,
                        value |-> m.value
                        ])
                 /\ UNCHANGED<<decision>>
                \* largest received so far < new ballot number
                \* Update value, update largest ballot number
                \* send old largest ballot number,
                \* send old value

\* Phase 3
PaxosDecide == /\ \E q \in PaxosQuorums, b \in Ballots, v \in Values, p \in Replicas:
                  /\ \A acc \in q : 
                        \E m \in FilterAcceptor(FilterProposer(P2bMessages, p),acc): /\ m.ballot = b
                                                                               /\ m.value = v
                  /\ SendMessage([type |-> "P3",ballot |-> b,value |-> v])
               /\ UNCHANGED<<decision>>

                \* Send decided value

PaxosDecided == \E msg \in P3Messages, a \in Replicas : DecideValue(a,msg.value)
                

PaxosInit == /\ messages = {}
             /\ decision = [r \in Replicas |-> None]

PaxosNext == \/ PaxosPrepare
             \/ PaxosPromise
             \/ PaxosAccept
             \/ PaxosAccepted
             \/ PaxosDecide
             \/ PaxosDecided

PaxosTypeOK == /\ None \notin Values
               /\ messages \subseteq Message
               /\ decision \in [Replicas -> Values \union {None}]

DecideConflict == \E a, b \in Replicas : /\ decision[a] # None
                                         /\ decision[b] # None
                                         /\ decision[a] # decision[b]

DecideChange == \E a \in Replicas : /\ decision[a] # None
                                    /\ decision[a] # decision'[a]

InvalidAccepted == \E m \in P2bMessages :
                       \/ m.ballot = None /\ m.value # None
                       \/ m.ballot # None /\ m.value = None
                       \/ /\ m.ballot # None \/ m.value # None
                          /\ \A n \in P2aMessages : /\ m.ballot # n.ballot
                                                    /\ m.value # n.value

PaxosSafetyProperty == /\ [][~DecideChange]_<<messages, decision>>
                       /\ [][~DecideConflict]_<<messages, decision>>
                       /\ [][~InvalidAccepted]_<<messages, decision>>

PaxosLivenessProperty == TRUE

PaxosSymmetry == Permutations(Values) \union Permutations(Replicas)

===============================================================