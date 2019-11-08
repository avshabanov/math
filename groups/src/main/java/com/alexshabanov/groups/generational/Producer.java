package com.alexshabanov.groups.generational;

public interface Producer<TElementDescription> {
  TElementDescription next(TElementDescription source);
}
