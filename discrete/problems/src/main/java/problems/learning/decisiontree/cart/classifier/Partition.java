package problems.learning.decisiontree.cart.classifier;

import lombok.Value;

import java.util.ArrayList;
import java.util.List;

/**
 * Represents partitioned training data sets.
 */
@Value(staticConstructor = "of")
public final class Partition {
  private List<TrainingData> trueRows;
  private List<TrainingData> falseRows;

  public static Partition run(List<TrainingData> rows, Question question) {
    final List<TrainingData> trueRows = new ArrayList<>(rows.size());
    final List<TrainingData> falseRows = new ArrayList<>(rows.size());

    for (final TrainingData row : rows) {
      if (question.match(row)) {
        trueRows.add(row);
      } else {
        falseRows.add(row);
      }
    }

    return of(trueRows, falseRows);
  }
}
