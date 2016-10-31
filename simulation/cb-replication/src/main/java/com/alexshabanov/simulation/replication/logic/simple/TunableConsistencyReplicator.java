package com.alexshabanov.simulation.replication.logic.simple;

/**
 * Replicator with tuneable consistency, e.g.:
 *  weaker, e.g. 1 host guaranteed write (fastest),
 *  weak, e.g. 2 hosts guaranteed write,
 *  sound, e.g. 3 hosts guaranteed write with eventual gossip to the others (usually durability/consistency optimal),
 *  strong, guaranteed write on all hosts (slowest).
 *
 * @author Alexander Shabanov
 */
public class TunableConsistencyReplicator {
}
