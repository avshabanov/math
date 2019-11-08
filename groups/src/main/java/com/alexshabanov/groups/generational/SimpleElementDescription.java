package com.alexshabanov.groups.generational;

import lombok.NonNull;

public interface SimpleElementDescription {
  boolean isLessThan(@NonNull SimpleElementDescription other);
}
