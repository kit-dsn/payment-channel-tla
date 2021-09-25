------------------------------- MODULE Ledger -------------------------------

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Users,
          Hashes,
          Time,
          Preimages,
          Amounts,
          IDs,
          Keys,
          SingleSignature,
          AllSignatures,
          SingleSigHashLock,
          AllSigHashLock

VARIABLES LedgerTx,
          LedgerTime,
          TIOUsedTransactionIds
          
Subset2(set) == {subset \in SUBSET set : Cardinality(subset) <= 2}
Subset(set, n) == {subset \in SUBSET set : Cardinality(subset) <= n}
          
ConditionData == [keys: SUBSET Keys] \cup [keys: SUBSET Keys, hash: Hashes]
Conditions == [type: {SingleSignature, AllSignatures, SingleSigHashLock, AllSigHashLock},
               data: ConditionData,
               absTimelock: Time,
               relTimelock: Time]
Signatures == SUBSET Keys

TimelockedWitness == [signatures: Signatures, absTimelock: Time]
Witnesses == [signatures: Signatures] \cup [signatures: Signatures, preimage: Preimages]
TransactionInputs == [parentId: IDs, outputId: IDs, witness: Witnesses]
TransactionOutputs == [parentId: IDs,
                       outputId: IDs,
                       amount: Amounts,
                       conditions: Subset(Conditions, 3)]
Transactions == [id: IDs,
                 inputs: Subset(TransactionInputs, 4),                                              \* TODO increase limits here for models with more than two concurrent transactions
                 outputs: Subset(TransactionOutputs, 4)]                                            \* TODO increase limits here
PublishedTransactions == [id: IDs,
                          inputs: Subset(TransactionInputs, 4),                                     \* TODO increase limits here
                          outputs: Subset(TransactionOutputs, 4),                                   \* TODO increase limits here
                          publishedAt: Time]

TypeOK == /\ LedgerTx \subseteq PublishedTransactions
          /\ \A tx \in LedgerTx : (\A output \in tx.outputs : output.parentId = tx.id)
          /\ LedgerTime \in Time
          
\* From https://learntla.com/libraries/sets/
Pick(S) == CHOOSE s \in S : TRUE
RECURSIVE SetReduce(_, _, _)
SetReduce(Op(_, _), S, value) == IF S = {} THEN value
                              ELSE LET s == Pick(S)
                              IN SetReduce(Op, S \ {s}, Op(s, value)) 
Sum(S) == LET _op(a, b) == a + b
          IN SetReduce(_op, S, 0)
\* End from https://learntla.com/libraries/sets/
SumAmounts(outputs) == LET _op(a, b) == a.amount + b
                       IN SetReduce(_op, outputs, 0)

LedgerTxIds == {tx.id : tx \in LedgerTx}

LedgerInputs(ledger) == UNION {tx.inputs : tx \in ledger}
LedgerOutputs(ledger) == UNION {tx.outputs : tx \in ledger}
LedgerOutputsWithParent(ledger) ==
    UNION { { [output |-> output, parent |-> tx] : output \in tx.outputs} : tx \in ledger }

ConfirmedParentTx(tx) == { parent \in LedgerTx :
                             (\E input \in tx.inputs : input.parentId = parent.id)}
OutputsSpentByInputs(inputs) ==
    { output \in LedgerOutputs(LedgerTx) :
        (\E input \in inputs :
            input.outputId = output.outputId /\ output.parentId = input.parentId) }

UnspentLedgerOutputs(ledger) ==
    {output \in LedgerOutputs(ledger) :
        (~\E input \in LedgerInputs(ledger) :
            /\ input.parentId = output.parentId
            /\ input.outputId = output.outputId)}
UnspentLedgerOutputsWithParent(ledger) ==
    {outputWithParent \in LedgerOutputsWithParent(ledger) :
        (~\E input \in LedgerInputs(ledger) :
            /\ input.parentId = outputWithParent.output.parentId
            /\ input.outputId = outputWithParent.output.outputId)}

         
\*UnspentOutputsOfTransaction(tx) ==
\*    { output \in tx.outputs :
\*        ~ \E child \in LedgerTx :
\*            \E input \in child.inputs :
\*                /\ input.parentId = tx.id
\*                /\ input.outputId = output.outputId
\*    }

AmountSpentByInputs(inputs) ==
    SumAmounts(OutputsSpentByInputs(inputs))

WitnessMatchesConditions(witness, conditions, parentPublishedAt, time) ==
    /\ conditions \in SUBSET Conditions
    /\ witness \in Witnesses
    /\ \E condition \in conditions : \* one condition needs to be fulfilled by the signature
        /\ condition.type \in {SingleSignature, SingleSigHashLock} =>
            (\E key \in condition.data.keys : key \in witness.signatures)
        /\ condition.type \in {AllSignatures, AllSigHashLock} =>
            (\A key \in condition.data.keys : key \in witness.signatures)
        /\ condition.type \in {SingleSigHashLock, AllSigHashLock} =>
            /\ "preimage" \in DOMAIN witness
            /\ condition.data.hash = witness.preimage
        /\ condition.absTimelock > 0 => time >= condition.absTimelock
        /\ condition.relTimelock > 0 => time >= parentPublishedAt + condition.relTimelock
    /\ witness \in TimelockedWitness => time >= witness.absTimelock

TxValid(tx, ledger) ==
    /\ \A output \in tx.outputs : output.parentId = tx.id
    /\ \A parent \in ConfirmedParentTx(tx) :
        /\ \A txInput \in tx.inputs : txInput.parentId = parent.id =>
            \A parentOutput \in parent.outputs :
                parentOutput.outputId = txInput.outputId =>
                    WitnessMatchesConditions(txInput.witness,
                                             parentOutput.conditions,
                                             parent.publishedAt,
                                             LedgerTime)
        /\ \A parentOutput \in parent.outputs :
            \* There is at most one child that is not the parent itself
            Cardinality(
                {spendingTx \in ledger :
                    \E input \in spendingTx.inputs :
                        /\ input.parentId = parent.id
                        /\ input.outputId = parentOutput.outputId
                } \ {parent}
            ) <= 1
    /\ \A input \in tx.inputs :
        \* circular transactions are only accepted at time 0 (in initial state)
        /\ tx.publishedAt > 0 => input.parentId # tx.id 
        /\ \E parent \in ConfirmedParentTx(tx) :
            \E parentOutput \in parent.outputs :
                /\ parentOutput.outputId = input.outputId
                /\ parent.id = input.parentId \* all referenced parents exist
    \* the transaction's outputs do not spend more than the inputs:
    /\ SumAmounts(tx.outputs) <= AmountSpentByInputs(tx.inputs)
    /\ AmountSpentByInputs(tx.inputs) > 0

PublishableTxForTx(tx) == [id |-> tx.id,
                           inputs |-> tx.inputs,
                           outputs |-> tx.outputs,
                           publishedAt |-> LedgerTime]

UnpublishedTxValid(tx, ledger) == 
    LET publishableTx == PublishableTxForTx(tx)
    IN TxValid(publishableTx, ledger \cup {publishableTx})

PublishTx(tx) ==
    /\ ~ tx.id \in  LedgerTxIds
    /\ LET publishedTx == PublishableTxForTx(tx)
       IN /\ LedgerTx' = LedgerTx \cup {publishedTx}
          /\ TxValid(publishedTx, LedgerTx')
          \* This should not be necessary and exists only to prevent errors in case of specification errors:
          /\ TIOUsedTransactionIds' = TIOUsedTransactionIds \cup {tx.id}

OnChainOutputSpendableByUser(ledger, inventory, time) ==
    {outputWithParent \in UnspentLedgerOutputsWithParent(ledger) :
        \/  \E preimage \in inventory.preimages :
                LET witness == [signatures |-> inventory.keys, preimage |-> preimage]
                IN WitnessMatchesConditions(witness,
                                            outputWithParent.output.conditions,
                                            outputWithParent.parent.publishedAt,
                                            time)
        \/  /\ Cardinality(inventory.preimages) = 0
            /\ LET witness == [signatures |-> inventory.keys]
               IN WitnessMatchesConditions(witness,
                                           outputWithParent.output.conditions,
                                           outputWithParent.parent.publishedAt,
                                           time)
    }
                 
SingleSignatureCondition(key) == [type |-> SingleSignature,
                                  data |-> [keys |-> {key}],
                                  absTimelock |-> 0,
                                  relTimelock |-> 0]
AllSignaturesCondition(keys) == [type |-> AllSignatures,
                                 data |-> [keys |-> keys],
                                 absTimelock |-> 0,
                                 relTimelock |-> 0]
SingleSigHashLockCondition(key, hash) == [type |-> SingleSigHashLock,
                                          data |-> [keys |-> {key},
                                                    hash |-> hash],
                                          absTimelock |-> 0,
                                          relTimelock |-> 0]
AllSigHashLockCondition(keys, hash) ==
    [type |-> AllSigHashLock,
     data |-> [keys |-> keys,
               hash |-> hash],
     absTimelock |-> 0,
     relTimelock |-> 0]

=============================================================================
\* Modification History
\* Last modified Fri Sep 24 18:48:43 CEST 2021 by matthias
\* Created Tue Apr 13 11:53:58 CEST 2021 by matthias
