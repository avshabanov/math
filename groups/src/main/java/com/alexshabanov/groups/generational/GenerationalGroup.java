package com.alexshabanov.groups.generational;

import lombok.NonNull;

/**
 * Generational group produces its element using algorithm as follows (pseudocode):
 * <code>
 *   1. left = right = identity
 *   2. set <- {left, right}
 *   3. left = LeftProducer(left)
 *   4. right = RightProducer(right)
 *   5. goto 2
 * </code>
 *
 * @param <TElementDescription> A description of the group's element.
 */
public interface GenerationalGroup<TElementDescription> {
  @NonNull TElementDescription getIdentity();
  @NonNull Producer<TElementDescription> getRightProducer();
  @NonNull Producer<TElementDescription> getLeftProducer();
}
