# Linearizability

Quote:

**Linearizability**

Linearizability is a recency guarantee on reads and writes of a register (an individual object).
It doesn't group operations together into transactions, so it does not prevent problems such as write skew..., 
unless you take additional measures such as materializing conflicts...

Not to be confused with:

**Serializability**

Serializability is an isolation property of transactions, where every transaction may read and write 
multiple objects (rows, documents, records)...
It guarantees that transactions behave the same as if they had executed in some serial order (each transaction running 
to completion before the next transaction starts). 
It is okay for that serial order to be different from the order in which transactions were actually run.

## Basic Idea

To make a system appear as if there is only a single copy of the data.
