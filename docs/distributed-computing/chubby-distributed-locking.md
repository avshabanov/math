# The Chubby Lock Service for Loosely-Coupled Systems

Summary as per

* [Official Paper](https://static.googleusercontent.com/media/research.google.com/en//archive/chubby-osdi06.pdf)
* [Medium Post](https://medium.com/coinmonks/chubby-a-centralized-lock-service-for-distributed-applications-390571273052)
* [Google Chubby Design on Slideshare](https://www.slideshare.net/romain_jacotin/the-google-chubby-lock-service-for-looselycoupled-distributed-systems)
* [Youtube Presentation Video](https://www.youtube.com/watch?v=kX9Z0F-eTt4)
* [Election in Chubby and Zookeeper](https://www.coursera.org/lecture/cloud-computing-2/1-3-election-in-chubby-and-zookeeper-IDKhR)

Goal is to provide a reliable service for coarse-grained locking.
A "coarse grained" term implies helding locks for hours or days, not seconds.

Typical use of Chubby is to elect a master, the first one getting the lock wins and becomes a master.

The main point is that lock service **reduces the number of servers** needed for a reliable client system to
make progress, e.g. as compared to Paxos.

## Paxos vs Lock Service

Lock service pros:

1. **Developer friendliness**: it is far easier to add locking semantics than consensus-based mechanics.
2. **Event notification with data**: most frequent use case: an application needs to write and read small amount of data in a consistent manner. 
3. **Application progress**: paxos requires majority of applications to be up to make progress. In centralized lock service even a single one would suffice
as long as it has correct access to locks.

## Design Decisions

1. **Coarse grained locking** — Applications don’t need locks of shorter duration. For example, electing a master is not a frequent event.
    * Long duration lock = low lock acquisition rate = less load on the lock server
2. **Small data storing** (small file manipulations) capabilities in addition to a lock service. Data stored reliably.
3. Allow **thousands of clients** to **observe changes**. So lock service needs to scale to handle many clients, although the transaction rate may not be that high.
4. **Notification mechanism** by which client knows when the change occurs in the file that is shared e.g. when a primary changes.
    * Avoid polling by clients that wish to know change
5. Support **client side caching** to deal with clients that may want to poll aggressively.
6. **Strong caching guarantees** to simplify developer usage.

Design emphasis:

* Availability
* Reliability

Out of scope:

* High performance / High throughput

Chubby uses asynchronous consensus: **PAXOS with lease timers** to ensure liveness.
Security Mechanisms in place - access controls.

In practice quorum election can span from 1 second (average case) to 30 seconds (worst case).

### System Structure

Two main components that interact via RPC:

* A replica server
* A library linked against client application

A Chubby cell consists of small set of servers (typically 5) known as replicas:

* Replicas use a distributed consensus protocol (PAXOS) to elect a master and replicate logs
* Read and write requests are satisfied by master alone
* If a master fails, other replicas run the election protocol when their master lease expire (new master elected in a few seconds)

Clients find the master by sending master location requests to the replicas listed in the DNS

* Non-master replicas respond by returning the identity of the master
* Once a client has located the master, client directs all requests to it until either it ceases to respond or until
it is no longer a master.

```text
+---------------------+
| DNS Servers:        |
| 8.8.8.8             |
| 8.8.4.4             |
+---------------------+
  ^
  | 1. DNS Request: Get A-record for chubby.deathstar.sith
  |    Sample Response: 10.0.0.1, 10.0.0.2, 10.0.0.3, 10.0.0.4, 10.0.0.5
  |
+-------------+-------+             
|   client    |chubby |  2. Get Master IP      
| application |library|-------------\  Sample Response: 10.0.0.5
+-------------+-------+              \
  |                                   v
  | 3. Initiates Chubby Session     +--------------------------+
  |    with Master                  |  1. 10.0.0.1 / replica   |
  |                                 |  2. 10.0.0.2 / replica   |
  |                                 |  3. 10.0.0.3 / replica   |
   \                                |  4. 10.0.0.4 / replica   |
    --------------------------------+> 5. 10.0.0.5 / master    |
                                    +--------------------------+
```

### Paxos Distributed Consensus

Chubby cell with N = 3 replicas: 

* Replicas use a distributed consensus protocol to elect a master (PAXOS). **Quorum = 2 for N = 3**
* The master must obtain votes from a majority of replicas that promise to not elect a different master 
for an interval of a few seconds (which is a **master lease**)
* The master lease is periodically renewed by the replicas provided the master continues to win a majority of  the vote
* During its master lease, the master maintains copies of a simple database with replicas (ordered replicated logs)
* Write request are propagated via the consensus protocol to all replicas (PAXOS)
* Read requests are satisfied by the master alone
* If a master fails, other replicas run the election protocol when their master lease expire (new master elected in few seconds)

```text
(Master)                (Replica 1)              (Replica 2)
    | Prepare                |                        |
    +----------------------->|                        |
    +------------------------------------------------>|
    |            Promise(1)  |                        |
    |<-----------------------+                        |
    |                        |                        |
[------- QUORUM ------------------------------------------] Promise from replica 2 is now unnecessary
    |                        |             Promise(2) |     is now unnecessary to progress further
    |<------------------------------------------------+
    |                        |                        |
===========================================================
    | Accept                 |                        |
    +----------------------->|                        |
    +------------------------------------------------>|
    | Accepted(0)            |                        |
    +----------------------->|                        |
    +------------------------------------------------>|
    |                        |                        |
    |           Accepted(1)  |                        |
    |<-----------------------+                        |
[------- QUORUM ------------------------------------------] Accept acknowledgement from replica 2
    |                        |            Accepted(2) |     is now unnecessary to progress further
    |<------------------------------------------------+
    |                        |            Accepted(2) |
    |                        |<-----------------------+
    |                        |                        |
===========================================================
```


* Prepare = please votes for me and promises not to vote for someone else during 12 seconds
* Promise = OK i vote for you and promise not to vote for someone else during 12 seconds if i received quorum of Promise
  then i am the Master and i can send many Accept during my lease (Proposer vote for himself)
* Accept = update your replicated logs with this Write client request
* Accepted = i have write in my log your Write client request if a replica received quorum of Accepted then the
  Write is commited (replica sends an Accepted to himself)
* Re‐Prepare = i love to be the Master, please re‐vote for me before the end the lease so i can extend my lease

## System Architecture

```text
                                   5 servers of a
                                    Chubby Cell
+-------------+-------+             +----------+
|   client    |chubby |    RPC      |     O    |
| application |library|-------------+--+> O    |   master
+-------------+-------+             |  /  O    |
                                ----+-/   O    |
+-------------+-------+        /    |     O    |
|   client    |chubby |-------/     +----------+
| application |library|
+-------------+-------+

   client processes
```

Components:

* Client library: executes locking protocol on client app's behalf.
    * Connect to a master for all the coordination needs.
    * Use DNS to find the master
    * Replicas respond to clients issuing DNS queries by redirecting the clients to the current master
    * Once client finds the master, all requests go to the master
    * Run the locking protocol on app's behalf and notify app of certain events such as master fail-over has occurred
* Servers: 1 master and 4 replicas.
    * Master is elected using distributed consensus protocol, e.g. like Paxos.
    * All replicas also grant a lease to the master
    * Master - writes to the DB any persistent state that is needed, which is then replicated at other replicas
    * Master needs to replicate a write at majority before acknowledging back to the client
    * If master fails, consensus protocol is again run to elect a new master.

## File-based Interface

Chubby exports UNIX file system like APIs. Files and directories are called nodes. No links allowed.
Nodes can be permanent or ephemeral. Ephemeral nodes go away as soon as there is no client using the node.
A file can be opened in a read/write mode indicating the exclusivity. Clients get a handle to the given node.
The following metadata is also allocated per node:

1. **Instance number** — always increasing for the same name
2. Content generation number — Increased anytime content is overwritten
3. Lock generation number — Increases when lock transitions from free to held
4. There also ACLs on nodes like in a traditional file system for controlling access and an ACL number increases on ACL changes.
5. Other types of metadata to deal with cases when a new master sees a handle that was generated by a previous master.

File Design Overview:

* Tree of files and directories with name components separated by slashes
* Each directory contains a list of child files and directories (collectively called nodes)
* Each file contains a sequence of uninterpreted bytes
* **No symbolic or hard links**
* No directory modified times, no last-access times (to make easier to cache file metadata)
* No path-dependent permission semantics: **file is controlled by the permissions on the file itself**

Example: `/ls/dc-tatooine/bigtable/root-tablet`

* The `ls` prefix is common to all Chubby names: stands for lock service.
* Second component `dc-tatooine` is the name of the Chubby cell. It is resolved to one or more Chubby servers via DNS lookup.  
* The remaining of the name is interpreted within the named Chubby cell.

Nodes (= files or directories) may be either permanent or ephemeral:

* Ephemeral files are used as temporary files, and act as indicators to others that a client is alive
* Any nodes may be deleted explicitly
    * Ephemeral nodes files are also deleted if no client has them open
    * Ephemeral nodes directories are also deleted if they are empty
* Any node can act as an advisory reader/writer lock

Metadata:

* 3 ACLs:
    * Three names of access control lists (ACL) used to control reading, writing and changing the ACL names for the node
    * Node inherits the ACL names of its parent directory on creation
    * ACLs are themselves files located in `/ls/dc-tatooine/acl` (ACL file consist of simple lists of names of principals)
    * Users are authenticated by a mechanism built into the Chubby RPC system
* 4 monotonically increasing 64-bit numbers:
    1. Instance number: greater than the instance number of any previous node with the same name
    2. Content generation number (files only): increases when the file's contents are written
    3. Lock generation number: increases when the node’s lock transitions from free to held
    4. ACL generation number: increases when the node’s ACL names are written
* 64-bit checksum

Handles:

* Clients open nodes to obtain Handles (analogous to UNIX file descriptors)

Handles include:

* **Check digits**: prevent clients from creating or guessing handles => full access control checks performed 
  only when handles are created
* **A sequence number**: Master can know whether a handle was generated by it or a previous master
* **Mode information**: (provided at open time) to allow the master to recreate its state if an old handle is 
  presented to a newly restarted master


## Locks, Lock-Delays and Sequencers

A client can create a node/file in a write (exclusive) or read (shared) mode.
All the locks are advisory i.e. participating entries need to follow the locking protocol for accesses the 
distributed critical section.

Having a lock on the file, doesn't prevent unfettered accesses to the file.

Resolving dead applications holding the locks:

```text
(client)                                                  (master)
   | 1        R1  Lock(N)                                     |
   +--------------------------------------------------------->|
   | 2                                  OK                    |
   |<---------------------------------------------------------+
   |                                                          |
   | 3        R2  Update(N)                                   |
   +-------------------------------x                          |
   | 4        R1 Dies                                         |
   |                                                          |
   | 5        R2  Lock(N)                                     |
   +--------------------------------------------------------->|
   | 6                                  OK                    |
   |<---------------------------------------------------------+ Now R2 holds the lock
   |                                                          |
   |                   R1 Recovers and redoes update(N)       |
   |                               x  R1 Update(N)            |
   |                               +------------------------->|
```

Simple (but not perfect) solution is to introduce a **lock-delay**. When an application holding the lock dies without
releasing the lock, for some configurable time, no one else gets a lock on the locks held by the now-defunct application.

Another possible solution: **sequencer based checking**. When a client acquires a lock, it can request for sequencer
from the chubby master. This is a string that consists of lock name, lock generation number (that changes on every
transition from free to held) and the mode of acquisition - `foo:1:exclusive`.
This string can be passed on to the modules needing the lock for protected transactions.
These modules can check for the validity of the lock using sequencers by checking against the chubby master or
using the module’s chubby cache.

Locks, Sequencers and Lock-delay:

* Each Chubby file and directory can act as a reader-writer lock (locks are advisory)
* Acquiring a lock in either mode requires write permission
    * **Exclusive mode** (writer): One client may hold the lock
    * **Shared mode** (reader): Any number of client handles may hold the lock
* Lock holder can request a **Sequencer**: opaque byte string describing the state of the lock immediately aher acquisition
    * Name of the lock + Lock mode (exclusive or shared) + Lock generation number
* Sequencer usage
    * Application's master can generate a sequencer and send it with any internal order sends to other servers
    * Application's servers that receive orders from a master can check with Chubby if the sequencer is 
      still good (= not a stale master)
* **Lock-delay**: Lock server prevents other clients from claiming the lock during lock-delay period if lock becomes free
    * client may specify any look-delay up to 60 seconds
    * This limit prevents a faulty client from making a lock unavailable for an arbitrary long time
    * Lock delay protects unmodified servers and clients from everyday problems caused by message delays and restarts 

## Detection of changes using events

Chubby allows some small aspects of a publish and subscribe mechanisms.
The following events are used:

* **File contents have changed**: Used to describe the new locations for the given service
* **Child node added to a directory**: Used for describe addition of a new replica
* **Chubby master fail-over**: Used for client to go into recovery mode
* **Invalid Handle**: Some communication issues

Summary:

Session events can be received by application:
* Jeopardy: when session lease timeout and grace period begins (related to fail-over)
* Safe: when the session is known to have survived a communication problem
* Expired: session timed out 

Handling events: clients may subscribe to a range of events when they create a Handle (=Open phase)
* File contents modified
* Child node added/removed/modified
* Master failed over
* A Handle (and it’s lock) has become invalid
* Lock acquired
* Conflicting lock request from another client

These events are delivered to the clients asynchronously via an update call from the Chubby library.

Mike Burrows: *The last two events mentioned are rarely used, and with hindsight could have been omitted*.

## Electing a primary using Chubby

Using the mechanisms described so far, client can now elect a primary:

* All the entities that want to become a master, try to open a file in write mode.
* Only one of those get the write mode access and others fail.
* The one with write access, then writes its identity to the file
* All the others get the file modification event and know about the the current master now.
* Primary uses either a sequencer or a lock-delay based mechanism to ensure that out-of-order messages don’t cause
inconsistent access and services can confirm if the sequencer for the current master is valid or not.

## Caching and Keep-Alive Calls

Client keeps a cache which is always consistent.
For writes, the write is propagated to the master and doesn’t complete until master acknowledges it. 
Master maintains state information about all the clients and hence can invalidate a client’s cache if someone else
writes to the same file.
The client that issued the write in such cases is blocked until all invalidations have been sent to the other clients 
and acknowledged by them.

There are KeepAlive calls that client makes to the master.
At any point, for a well behaving client, there will always be one outstanding KeepAlive call at the master.
Basically a client acknowledges master’s response by issuing the next KeepAlive call.
Server can send some information back as a response of this call at a later time e.g. an invalidation can be sent to 
the client as response of a prior KeepAlive call.
Client will see the response and then invalidate its own cache and then open another KeepAlive call at the master for 
future communication from the master. 
Another advantage of this mechanism is that no additional holes need to be punched in the firewalls.
Outbound calls from clients are generally allowed and clients don't need to open and listen on ports for the master to
initiate connections to clients.

## Sessions

We discussed KeepAlive RPCs in the last section. These establish a client-master chubby session.
When a client makes this KeepAlive call to the master, master blocks this call.
Master then also assigns a lease to the client. This master lease guarantees that the master won't unilaterally
terminate this session. When the lease is about to expire or if there is some event to which the client is subscribed,
master can use this blocked call for sending the information back. In the former case, master may extend the lease or
in the later case master can send information such as which files have changed.

Clients cannot be sure if the master is alive and the lease that the client has is still valid.
So clients keep a slightly smaller local lease timeout. If this timeout occurs and master hasn't responded,
then client isn't sure if the master is still around and if its local lease is valid.
At this time, client considers that it's session is in jeopardy and starts the grace period.
It also disables its cache. If client heard back from the master during the grace period (45s), then the client
can enable the cache once more. If client doesn't hear back from the master then it is assumed the master is
inaccessible and clients return errors back to the application. Applications get informed about both jeopardy and
expired events from the chubby client library.

## Master Fail-over

One of the most disruptive events that can happen is that the master fails for a considerable time and a new master
gets elected after some time. Let’s look at how that sequence looks like.
Local lease timeouts, jeopardy-grace periods trigger during this time at the client.
All clients using this master need to switch over to the new master and new master needs to recreate the state
information about the clients using the replicated database that master uses to manage the persistent state.

Let’s walk through all the vertical slanted KeepAlive calls from left to right.

* KA1: Client makes the call. No leases have been assigned yet. Master assigns lease M1. Client currently has the lease C1.
* KA2: In the response toe KA1, a smaller local lease C2 is assigned for the client. Master also extends its lease to M2.
* KA3: Client acknowledges KA2 and makes the RPC call that needs to be outstanding at the master. Master dies after getting the call. So no new leases can be assigned. Client’s C2 lease expires and client library informs the application that it has entered jeopardy. The grace period starts on the client.
* KA4: In the meanwhile a new master gets elected and clients get notified about it. The new master gets this KA4 message and it responds back. Master also assigns lease M3 conservatively based on previous master’s lease promises — remember that client caching is dependent on this.
* KA5: Master doesn’t know if this is just a delayed packet or really an attempt by the client to establish a new session. For this master uses an epoch number and if it notices an old epoch number(which clients send to the master) then that call doesn’t actually extend the lease on either side and the response is one of rejection.
* KA6: This one uses the new epoch number sent by the master. So succeeds, but leases are not yet extended by the master.
* KA7: This one allows the client to extend its local lease to C3. Now client is out of jeopardy and can exit the grace period.
* KA8: This one again keeps the session alive with the master and we are back to normal operations. Since all of this happened before the grace period ended, application didn’t see any errors. If KA6 had happened after the grace period was over, application would have seen the errors.

A new master that gets elected goes through a fairly detailed process of reconstruction. This seems like a pretty tricky code to get right. At a high level:

* Master creates the epoch number mentioned above
* Reconstructs the in-memory state about client leases etc. by reading the database maintained by the last master
* Now it stops rejecting KeepAlive session requests only. Everything else is still being rejected.
* Sends out fail-over event information to clients. Clients can then invalidate their cache because some events might have been missed.
* After all client acknowledge or timeout, systems seems to be in a stable state and all other RPCs are allowed by the master

## API
 
Open/Close node name

* `func Open()` Handles are created by Open() and destroyed by Close()
* `func Close()` This call never fails
* `func Poison()` Allows a client to cancel Chubby calls made by other threads without fear of deallocating the memory
  being accessed by them
  
Read/Write full contents

* `func GetContentsAndStat()` Atomic reading of the entire content and metadata
* `func GetStat()` Reading of the metadata only
* `func ReadDir()` Reading of names and metadata of the directory
* `func SetContents()` Atomic writing of the entire content

ACL:

* `func SetACL()` Change ACL for a node

Delete node:

* `func Delete()` if it has no children

Lock: 

* `func Acquire()` Acquire a lock
* `func TryAcquire()` Try to acquire a potentially conflicting lock by sending "conflicting lock request" to the holder
* `func Release()` Release a lock

Sequencer:

* `func SetSequencer()` Returns a sequencer that describes any lock held by this Handle
* `func GetSequencer()` Associate a sequencer with a Handle.
  Subsequent operations on the Handle failed if the sequencer is no longer valid
* `func CheckSequencer()` Checks whether a sequencer is valid

## Conclusion

I found the idea of a centralized coordination service with locking semantics very useful.
Rather than participating in consensus based mechanisms, the locking semantics seem to simplify development of
applications in distributed environments as most developers are very familiar with those.
Also the way server and client protocol operates via client side libraries and related callbacks,
presents a nice mechanism to abstract intricacies of the protocol from the applications and allows for
easier integration.

## Appendix: Uses

* Distributed lock service (obviously)
* Name service.

## Appendix: Inferred API

From the official paper:
Client is ~7000 LOC of C++ code.

### KeepAlive

93% rate.

TCP's back off policies pay no attention to higher-level timeouts such as Chubby leases, so TCP-based KeepAlives
led to many lost sessions at times of high network congestion.
It was more desirable to use UDP rather than TCP as UDP has no congestion avoidance mechanism.

### GetStat

2% rate.
Similar to unix stat.

### Open

1% rate.
Similar to unix open.

### CreateSession

1% rate.

### GetContentsAndStat

0.4% rate.

### SetContents

680 ppm.

### Acquire

31 ppm.

## Implementation Hints

* C++
* Initially: Berkeley DB with custom replication

## Comparison with Related Work

* Cache design - distributed file systems.
* Sessions and cache tokens - similar to behavior to those in Echo.
* Sessions reduce the overhead of leases in the System V system.
* Idea of exposing a general-purpose lock service is found in VMS.

## Appendix: Open Source Alternatives to ZooKeeper

Top Alternatives to ZooKeeper:

* Eureka.
* HashiCorp Consul.
* Docker hub.
* SkyDNS.
* etcd.
* Hysterix.
* runc.
* SmartStack.


