package com.alexshabanov.nn.f1;

import com.alexshabanov.nn.f1.ofn.NeuralNetworkMetadata;
import com.alexshabanov.nn.f1.ofn.SimpleNeuralNetwork;
import com.alexshabanov.nn.f1.ofn.TrainingData;
import lombok.AllArgsConstructor;
import lombok.Getter;

import java.io.DataInputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.zip.GZIPInputStream;

/**
 * Main entry point.
 */
public final class ClassifyMainF1 {

  public static void main(String[] args) throws Exception {
    if (args.length < 1) {
      throw new IllegalArgumentException("Unexpected arg count: first arg should be a path to gzipped MNIST data." +
          " See also http://yann.lecun.com/exdb/mnist/");
    }
    final String folder = args[0];

    if (args.length > 1 && "-debugLoader".equals(args[1])) {
      final IdxImages images = readImageData(folder + File.separatorChar + "t10k-images-idx3-ubyte.gz", 10);
      complementLabelData(folder + File.separatorChar + "t10k-labels-idx1-ubyte.gz", images);
      images.dump();
      return;
    }

    final IdxImages images = readImageData(folder + File.separatorChar + "train-images-idx3-ubyte.gz",
        Integer.MAX_VALUE);
    complementLabelData(folder + File.separatorChar + "train-labels-idx1-ubyte.gz", images);
    System.out.println("Read " + images.images.size() + " image(s)");

    final List<TrainingData> trainingDataSet = images.toTrainingData();
    final NeuralNetworkMetadata metadata;
    if (args.length > 1 && "-withAbsInvFunction".equals(args[1])) {
      metadata = NeuralNetworkMetadata.withAbsInvFunction();
    } else {
      metadata = NeuralNetworkMetadata.withLogisticsFunction();
    }
    final SimpleNeuralNetwork neuralNetwork = new SimpleNeuralNetwork(metadata, new int[] {784, 100, 10});
    neuralNetwork.stochasticGradientDescent(trainingDataSet, 30, 10, 3.0f, true);

    // now test the network using first few images
    System.out.println("Test network:");
    for (int i = 0; i < Math.min(10, trainingDataSet.size()); ++i) {
      final TrainingData td = trainingDataSet.get(i);
      final float[] output = neuralNetwork.evaluate(td.getInput());
      System.out.println("Image #" + i + ", expected label: " + images.labels[i]);
      System.out.println("\tGot output=" + floatsToString(output) + ", expected=" + floatsToString(td.getOutput()));
    }

    int mismatches = 0;
    for (final TrainingData td : trainingDataSet) {
      final float[] output = neuralNetwork.evaluate(td.getInput());
      for (int j = 0; j < output.length; ++j) {
        if (Math.abs(output[j] - td.getOutput()[j]) > 0.4) {
          ++mismatches;
          break;
        }
      }
    }
    System.out.println(String.format("Match quality: %.2f percent(s)",
        (100.0 * (trainingDataSet.size() - mismatches)) / trainingDataSet.size()));
  }

  private static IdxImages readImageData(String filePath, int limit) throws IOException {
    try (final FileInputStream fileInputStream = new FileInputStream(new File(filePath))) {
      try (final GZIPInputStream gzipInputStream = new GZIPInputStream(fileInputStream)) {
        try (final DataInputStream dataInputStream = new DataInputStream(gzipInputStream)) {
          final IdxImagesHeader header = IdxImagesHeader.read(dataInputStream);
          final List<byte[]> images = new ArrayList<>(header.numberOfImages);
          for (int count = 0; count < limit && count < header.numberOfImages; ++count) {
            final byte[] image = new byte[header.numberOfRows * header.numberOfColumns];
            dataInputStream.readFully(image);
            images.add(image);
          }
          return new IdxImages(header, images, new int[header.numberOfImages]);
        }
      }
    }
  }

  private static void complementLabelData(String filePath, IdxImages images) throws IOException {
    try (final FileInputStream fileInputStream = new FileInputStream(new File(filePath))) {
      try (final GZIPInputStream gzipInputStream = new GZIPInputStream(fileInputStream)) {
        try (final DataInputStream dataInputStream = new DataInputStream(gzipInputStream)) {
          final IdxLabelHeader header = IdxLabelHeader.read(dataInputStream);
          if (header.numberOfItems != images.header.numberOfImages) {
            throw new IllegalStateException("unexpected labels data, expect " + images.header.numberOfImages +
                " labels, got " + header.numberOfItems);
          }

          for (int i = 0; i < header.numberOfItems; ++i) {
            images.labels[i] = dataInputStream.readByte();
          }
        }
      }
    }
  }

  /**
   * Format:
   * <pre>
   *   [offset] [type]          [value]          [description]
   *   0000     32 bit integer  0x00000803(2051) magic number
   *   0004     32 bit integer  60000            number of images
   *   0008     32 bit integer  28               number of rows
   *   0012     32 bit integer  28               number of columns
   *   0016     unsigned byte   ??               pixel
   *   0017     unsigned byte   ??               pixel
   *   ........
   *   xxxx     unsigned byte   ??               pixel
   * </pre>
   *
   * See also
   */
  static final class IdxImagesHeader {
    private static final int MAGIC = 0x00000803;

    int magic;
    int numberOfImages;
    int numberOfRows;
    int numberOfColumns;

    public static IdxImagesHeader read(DataInputStream dataInputStream) throws IOException {
      final IdxImagesHeader header = new IdxImagesHeader();
      header.magic = dataInputStream.readInt();
      if (header.magic != MAGIC) {
        throw new IOException("Unable to read header: magic mismatch, expect " + MAGIC + ", got " + header.magic);
      }

      header.numberOfImages = dataInputStream.readInt();
      header.numberOfRows = dataInputStream.readInt();
      header.numberOfColumns = dataInputStream.readInt();

      return header;
    }
  }

  @Getter
  @AllArgsConstructor
  static final class IdxImages {
    final IdxImagesHeader header;
    final List<byte[]> images;
    final int[] labels;

    List<TrainingData> toTrainingData() {
      final List<TrainingData> trainingData = new ArrayList<>(images.size());
      for (int i = 0; i < images.size(); ++i) {
        final float[] input = new float[784];
        final byte[] image = images.get(i);
        if (image.length != input.length) {
          throw new IllegalStateException("Unexpected image length");
        }
        for (int j = 0; j < input.length; ++j) {
          input[j] = (1.0f * Byte.toUnsignedInt(image[j])) / 255;
        }

        final float[] output = new float[10];
        output[labels[i]] = 1.0f;
        trainingData.add(new TrainingData(input, output));
      }
      return trainingData;
    }

    void dump() {
      System.out.println(String.format("Header: numberOfImages=%d, numberOfColumns=%d, numberOfRows=%d",
          header.numberOfImages, header.numberOfColumns, header.numberOfRows));

      for (int i = 0; i < images.size(); ++i) {
        final byte[] image = images.get(i);
        System.out.println("Image of number " + labels[i]);
        for (int y = 0; y < header.numberOfRows; ++y) {
          for (int x = 0; x < header.numberOfColumns; ++x) {
            byte b = image[x + y * header.numberOfColumns];
            System.out.print(String.format("%02X", b));
          }
          System.out.println();
        }

        System.out.println();
      }
    }
  }

  /**
   * Format:
   * <pre>
   *   [offset] [type]          [value]          [description]
   *   0000     32 bit integer  0x00000801(2049) magic number (MSB first)
   *   0004     32 bit integer  60000            number of items
   *   0008     unsigned byte   ??               label
   *   0009     unsigned byte   ??               label
   *   ........
   *   xxxx     unsigned byte   ??               label
   * </pre>
   *
   * See also http://yann.lecun.com/exdb/mnist/
   */
  static final class IdxLabelHeader {
    private static final int MAGIC = 0x00000801;

    int magic;
    int numberOfItems;

    public static IdxLabelHeader read(DataInputStream dataInputStream) throws IOException {
      final IdxLabelHeader header = new IdxLabelHeader();
      header.magic = dataInputStream.readInt();
      if (header.magic != MAGIC) {
        throw new IOException("Unable to read header: magic mismatch, expect " + MAGIC + ", got " + header.magic);
      }

      header.numberOfItems = dataInputStream.readInt();

      return header;
    }
  }

  public static String floatsToString(float[] arr) {
    final StringBuilder sb = new StringBuilder(arr.length * 7 + 10).append('[');
    for (int i = 0; i < arr.length; ++i) {
      if (i > 0) {
        sb.append(", ");
      }
      sb.append(String.format("%.2f", arr[i]));
    }
    return sb.append(']').toString();
  }
}
