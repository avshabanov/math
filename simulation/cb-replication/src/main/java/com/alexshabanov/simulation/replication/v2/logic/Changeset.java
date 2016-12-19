package com.alexshabanov.simulation.replication.v2.logic;

import java.io.Externalizable;

/**
 * @author Alexander Shabanov
 */
public interface Changeset extends Externalizable {

  String getEntityName();

  long getSequenceId();
}
