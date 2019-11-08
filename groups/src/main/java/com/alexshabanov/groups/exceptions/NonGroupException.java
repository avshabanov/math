package com.alexshabanov.groups.exceptions;

/**
 * Exception, thrown when certain group's property is violated.
 */
public class NonGroupException extends RuntimeException {
  public NonGroupException(String message) {
    super(message);
  }
}
