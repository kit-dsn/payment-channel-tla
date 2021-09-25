------------------------ MODULE TransactionIdOracle ------------------------

EXTENDS Naturals, FiniteSets

VARIABLES TIOUsedTransactionIds,
          AvailableTransactionIds
   
TypeOK == TIOUsedTransactionIds \in SUBSET Nat

GetNewTransactionId == CHOOSE id \in AvailableTransactionIds : ~ id \in TIOUsedTransactionIds

GetNewTransactionIds(count, disallow) == CHOOSE set \in SUBSET(AvailableTransactionIds \ (disallow \cup TIOUsedTransactionIds)) : Cardinality(set) = count

MarkMultipleAsUsed(newTransactionIds) == TIOUsedTransactionIds' = TIOUsedTransactionIds \cup newTransactionIds
MarkAsUsed(newTransactionId) == MarkMultipleAsUsed({newTransactionId})

=============================================================================
\* Modification History
\* Last modified Thu Sep 23 16:01:09 CEST 2021 by matthias
\* Created Mon Apr 12 17:34:51 CEST 2021 by matthias
