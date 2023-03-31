-------------------------------- MODULE HDFS --------------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Blocks, Replication

ASSUME Replication \in Nat

VARIABLES data, name, isAvail, requestedData

vars == <<data, name, isAvail, requestedData>>


\* Helper Operators

\* asserts that there are at least m nodes available
NumNodesAvailIsAtLeast(m) ==
    \E availNodes \in SUBSET Nodes :
        /\ Cardinality(availNodes) = m
        /\ \A n \in availNodes : isAvail[n]

\* at least Replication nodes are up and available
EnoughNodesAvailable == NumNodesAvailIsAtLeast(Replication)


\* System Definition

Init ==
    /\ data = [n \in Nodes |-> {}]
    /\ name = [b \in Blocks |-> {}]
    /\ isAvail = [n \in Nodes |-> TRUE]
    /\ requestedData = {}

StoreBlock(block) ==
    \E storageNodes \in SUBSET Nodes :
        /\ Cardinality(storageNodes) = Replication
        /\ \A n \in storageNodes : isAvail[n]
        /\ name' = [name EXCEPT![block] = name[block] \cup storageNodes]
        /\ data' = [n \in Nodes |-> IF n \in storageNodes
                                    THEN data[n] \cup {block}
                                    ELSE data[n]]
        /\ requestedData' = requestedData \cup {block}
        /\ UNCHANGED isAvail

NodeGoesDown(n) ==
    LET backups == {<<block,backup>> \in (Blocks \X Nodes) :
                        /\ backup # n
                        /\ isAvail[backup]
                        /\ ~(block \in data[backup])
                        /\ block \in data[n]}
    IN
    /\ isAvail[n]
    \* this condition below guarantees we found a backup for each block in n's data
    /\ \A d \in data[n] : \E backup \in Nodes : <<d,backup>> \in backups
    /\ isAvail' = [isAvail EXCEPT![n] = FALSE]
    /\ data' = [n1 \in Nodes |-> IF \E block \in Blocks : <<block,n1>> \in backups
                                 THEN data[n1] \cup {block \in Blocks : <<block,n1>> \in backups}
                                 ELSE data[n1]]
    /\ name' = [block \in Blocks |-> IF block \in data[n]
                                     THEN name[block] \cup {backup \in Nodes : <<block,backup>> \in backups}
                                     ELSE name[block]]
    /\ UNCHANGED<<requestedData>>

Next ==
    \/ \E block \in Blocks : StoreBlock(block)
    \/ \E n \in Nodes : NodeGoesDown(n)

Spec == Init /\ [][Next]_vars


\* System Invariants

TypeOK ==
    /\ data \in [Nodes -> SUBSET Blocks]
    /\ name \in [Blocks -> SUBSET Nodes]
    /\ isAvail \in [Nodes -> BOOLEAN]
    /\ requestedData \in SUBSET Blocks

\* we only guarantee redundancy if there's enough nodes available in the system
BlocksAreRedundant ==
    EnoughNodesAvailable =>
        \A block \in requestedData :
        \E availNodes \in SUBSET Nodes :
            /\ Cardinality(availNodes) = Replication
            /\ \A n \in availNodes : isAvail[n]
            /\ \A n \in availNodes : block \in data[n]

NameMapIsCorrect ==
    \A n \in Nodes :
    \A block \in Blocks :
        (n \in name[block]) <=> (block \in data[n])

=============================================================================
\* Modification History
\* Last modified Fri Mar 31 13:36:41 EDT 2023 by idardik
\* Created Fri Mar 31 11:25:38 EDT 2023 by idardik
