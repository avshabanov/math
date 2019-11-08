package com.alexshabanov.groups.finite;

/**
 * Exception, thrown when certain group's property is violated.
 */
public class NonGroupException extends RuntimeException {
  public NonGroupException(String message) {
    super(message);
  }
}
