package problems.conc.dl.api;

import lombok.Builder;
import lombok.NonNull;
import lombok.Value;
import lombok.experimental.UtilityClass;

import java.time.Instant;
import java.util.List;
import java.util.concurrent.TimeUnit;

/**
 * Lock service API
 */
@UtilityClass
public final class LockClient  {

  public final int O_TMPFILE = 1;
  public final int O_RDWR = 1 << 2;
  public final int O_WRONLY = 1 << 3;
  public final int O_CREAT = 1 << 4;
  public final int O_TRUNC = 1 << 5;
  public final int O_RDONLY = 1 << 6;

  public interface Locks {
    @NonNull Handle acquire(@NonNull String name, @NonNull RemoteFileMode mode, @NonNull LockRequest lockRequest);
    void release(Handle rfd);
  }

  public interface RemoteFiles {
    @NonNull Handle open(@NonNull String name, int mode, @NonNull LockRequest lockRequest);

//  default @NonNull Handle creat(String name) {
//    return open(name, O_CREAT | O_WRONLY | O_TRUNC);
//  }

    Stat getStat(@NonNull Handle rfd);

    byte[] getContents(@NonNull Handle rfd);

    ContentsAndStat getContentsAndStat(@NonNull Handle rfd);

    List<Stat> readDir(@NonNull String path);

    void setContents(@NonNull Handle rfd, byte[] contents);

    void close(@NonNull Handle rfd);

    // TODO: ACL
    //void setAcl(@NonNull Handle rfd, int acl);
  }

  public interface Sessions {

    void keepAlive(@NonNull Handle rfd);
  }

  @Value
  public static class Handle {
    String id;
  }

  @Value
  @Builder
  public static class RemoteFileMode {
    @Builder.Default
    int mode = O_RDONLY;

    // lifetime for new files, taken into an account only when file is created
    // -1 means: inherit dir settings
    @Builder.Default
    long maxLifetimeInSeconds = TimeUnit.HOURS.toSeconds(1);
  }

  @Value
  public static class LockRequest {
    long timeoutMillis;
    long maxHeartbeatDelay;
  }

  @Value
  public static class Stat {
    @NonNull String name;
    @NonNull Instant mtime; // last modification time
    int mode; // mode bits
    long size;
    Object sys;
  }

  @Value
  static class ContentsAndStat {
    @NonNull byte[] contents;
    @NonNull Stat stat;
  }

  /*
  TODO: ACL
  option 1 - https://github.com/kildevaeld/go-acl
  a := acl.NewAcl(acl.NewMemoryStore())

  // use case 1 - establish roles:
  a.Role("guest","")
  a.Role("user", "guest") // user inherits guest
  a.Role("admin", "user") // admin inherits user and guest

  // use case 2 - establish policies:
  a.Allow([]string{"user", "admin"}, "comment", "blog") // multiple
  a.Allow("guest", "read", "blog")

  // use case 3 - verify access
  a.Can("user", "comment", "blog") // true
  a.Can([]string{"user"}, "read", "blog") // true
  a.Can([]string{"guest"}, "comment", "blog") // false

  option 2 (simple) - https://zookeeper.apache.org/doc/r3.1.2/zookeeperProgrammers.html#sc_zkDataModel_znodes
  Excerpt:
  ACL Permissions
  ZooKeeper supports the following permissions:

  CREATE: you can create a child node
  READ: you can get data from a node and list its children.
  WRITE: you can set data for a node
  DELETE: you can delete a child node
  ADMIN: you can set permissions

  The CREATE and DELETE permissions have been broken out of the WRITE permission for finer grained access controls.
  The cases for CREATE and DELETE are the following:
  You want A to be able to do a set on a ZooKeeper node, but not be able to CREATE or DELETE children.
  CREATE without DELETE: clients create requests by creating ZooKeeper nodes in a parent directory.
  You want all clients to be able to add, but only request processor can delete. (This is kind of like the APPEND permission for files.)
  Also, the ADMIN permission is there since ZooKeeper doesn’t have a notion of file owner.
  In some sense the ADMIN permission designates the entity as the owner.
  ZooKeeper doesn’t support the LOOKUP permission (execute permission bit on directories to allow you to
  LOOKUP even though you can't list the directory). Everyone implicitly has LOOKUP permission.
  This allows you to stat a node, but nothing more.
  (The problem is, if you want to call zoo_exists() on a node that doesn't exist, there is no permission to check.)

  Builtin ACL Schemes
  ZooKeeeper has the following built in schemes:
  world has a single id, anyone, that represents anyone.
  auth doesn't use any id, represents any authenticated user.
  digest uses a username:password string to generate MD5 hash which is then used as an ACL ID identity.
  Authentication is done by sending the username:password in clear text. When used in the
  ACL the expression will be the username:base64 encoded SHA1 password digest.
  host uses the client host name as an ACL ID identity. The ACL expression is a hostname suffix.
  For example, the ACL expression host:corp.com matches the ids host:host1.corp.com
  and host:host2.corp.com, but not host:host1.store.com.
  ip uses the client host IP as an ACL ID identity.
  The ACL expression is of the form addr/bits where the most significant bits of addr are
  matched against the most significant bits of the client host IP.

  Unix ACL:
  https://www.redhat.com/sysadmin/linux-access-control-lists
  */

  /*
  Paper:
  https://static.googleusercontent.com/media/research.google.com/en//archive/chubby-osdi06.pdf

  Sample Metrics:

  TimeSinceLastFailOver: 18 days
  FailOverDuration: 14 seconds

  ActiveClients: 22000
  ProxyClients: 32000

  ClientIsCachingFileEntries: 2300000
  DistinctFilesCached: 24000
  NamesNegativelyCached: 32000

  ExclusiveLocks: 1000
  SharedLocks: 0

  StoredDirectories: 8000
  StoredEphemeralDirectories: 8

  StoredFiles: 22000
  StoredFiles 0..1 kB: 90%
  StoredFiles 1..10 kB: 10%
  StoredFiles 10 and more kB: 0.2%
  StoredFiles naming-related: 46%
  StoredFiles mirrored ACLs and config info: 27%
  StoredFiles GFS and Bigtable Metadata: 11%
  StoredFiles Ephemeral: 3%

  RPC Rate: 1-2k/s
    KeepAlive: 93%
    GetStat: 2%
    Open: 1%
    CreateSession: 1%
    GetContentsAndStat: 0.4%
    SetContents: 680ppm
    Acquire: 31ppm
   */

  /*
  Problems:

  * Client library is complicated; it further emphasizes the careful choice of supported languages
  * Data must fit in RAM
  * Abusive clients / noisy neighbor problems
    * => need storage and RPC quotas
  * Lack of caching
   */
}
