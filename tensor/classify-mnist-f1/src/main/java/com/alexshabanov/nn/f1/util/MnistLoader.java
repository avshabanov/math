package com.alexshabanov.nn.f1.util;

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
 * Encapsulates MNIST data loader.
 */
public final class MnistLoader {
  private MnistLoader() {}

  public static IdxImages load(String imageDataFile, String labelDataFile) throws IOException {
    final IdxImages images = readImageData(imageDataFile, Integer.MAX_VALUE);
    complementLabelData(labelDataFile, images);
    System.out.println("Read " + images.getImages().size() + " image(s) for dataFile=" + imageDataFile);
    return images;
  }

  private static IdxImages readImageData(String filePath, int limit) throws IOException {
    try (final FileInputStream fileInputStream = new FileInputStream(filePath)) {
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
    try (final FileInputStream fileInputStream = new FileInputStream(filePath)) {
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
  public static final class IdxImagesHeader {
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
  public static final class IdxImages {
    final IdxImagesHeader header;
    final List<byte[]> images;
    final int[] labels;

    public List<TrainingData> toTrainingData() {
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

    public void dump(int limit) {
      System.out.printf("Header: numberOfImages=%d, numberOfColumns=%d, numberOfRows=%d%n",
          header.numberOfImages, header.numberOfColumns, header.numberOfRows);

      for (int i = 0; i < limit; ++i) {
        final byte[] image = images.get(i);
        System.out.println("Image of number " + labels[i]);
        for (int y = 0; y < header.numberOfRows; ++y) {
          for (int x = 0; x < header.numberOfColumns; ++x) {
            byte b = image[x + y * header.numberOfColumns];
            System.out.printf("%02X", b);
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
  public static final class IdxLabelHeader {
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
}
