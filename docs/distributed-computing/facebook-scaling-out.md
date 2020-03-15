# Facebook Scaling Out

Published on `August 20, 2008 at 11:05 AM`, orgininal post: [Scaling Out](https://www.facebook.com/notes/facebook-engineering/scaling-out/23844338919/).

## Context

Single DC in CA. Scaling out requires opening another DC in IAD, in order to:

* Save 70ms roundtrip between west coast and east coast.
* Provide better latency for EU customers.
* Address DC space, power and disaster recovery concerns.

Existing architecture:

```text
           +----------+
           |Web Server|
           +----------+
           /           \
          |            |
          v            v
+----------+          +-----------+
|  My Sql  |          | Memcached |
+----------+          +-----------+
``` 

In IAD: My SQL works in R/O mode, there is a replication channel between CA and IAD. 

Challenges:

* Cache Consistency
* Traffic Routing

Cache consistency stems from the existing architecture assuming that memcached will be updated upon
successful update in MySQL. I.e.:

```text
// web server code
Response processWriteRequest(r) {
  mysql.write(r.key, r.value)
  memcached.delete(r.key)
}

Response processReadRequest(r) {
  value = memcached.read(r.key)
  if value is present {
    return value
  }
 
  // due to replication lag may reintroduce a value
  value = mysql.read(r.key)
  memcached.write(r.key, value)
  return value
}
```

Problem: replication lags coupled with caching behavior could result in constant cache inconsistency in worst case scenarios.
Solution: SQL extension that conveyed cache cleanups to reduce cache inconsistencies to near-zero.

## Page Routing

Problem: only master DBs in CA could accept writes.
Solution: introduce a cookie showing when update was made and reroute reads to masters if it was recent.
