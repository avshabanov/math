using System;
using System.Text;
using System.Diagnostics;

public sealed class KnightTour
{
    public const int DEFAULT_BOARD_SIDE_SIZE = 8;
    public const int DEFAULT_START_ROW = 0;
    public const int DEFAULT_START_COLUMN = 0;
    public const int DEFAULT_ITERATIONS = 1;

    public static void Main(string[] args)
    {
        var rows = GetArgParam(args, 0, DEFAULT_BOARD_SIDE_SIZE);
        var columns = GetArgParam(args, 1, DEFAULT_BOARD_SIDE_SIZE);
        var iterations = GetArgParam(args, 2, DEFAULT_ITERATIONS);

        Console.WriteLine("KnightTour <rows> <columns> <iterations>\n" +
                          "Using rows={0}, columns={1}, iterations={2}", rows, columns, iterations);

        for (var j = 0; j < iterations; ++j)
        {
            FindSolution(rows, columns, DEFAULT_START_ROW, DEFAULT_START_COLUMN);
        }
    }

    private static int GetArgParam(string[] args, int index, int defaultValue)
    {
        return index < args.Length ? Convert.ToInt32(args[index]) : defaultValue;
    }

    private static void FindSolution(int rows, int columns, int startRow, int startColumn)
    {
        var finder = new SolutionFinder(rows, columns);
        var watch = new Stopwatch();
        watch.Start();
        var found = finder.Move(startRow, startColumn, 1);
        watch.Stop();
        var elapsed = watch.Elapsed;

        Console.WriteLine("Solution {0}\nTime: {1}",
                          found ? ("Found: " + finder) : "Not Found",
                          elapsed);
    }
}

public sealed class SolutionFinder
{
    private static readonly Move[] KNIGHT_MOVES = new Move[]
    {
        new Move(2, 1), new Move(1, 2), new Move(-1, 2), new Move(-2, 1),
        new Move(-2, -1), new Move(-1, -2), new Move(1, -2), new Move(2, -1)
    };

    private readonly int rows;
    private readonly int columns;
    private readonly int[,] board;
    private readonly int maxMoves;

    public SolutionFinder(int columns, int rows) 
    {
        this.columns = columns;
        this.rows = rows;
        this.board = new int[rows, columns];
        this.maxMoves = columns * rows;
    }

    private bool IsLegalMove(int row, int column)
    {
        return row >= 0 && column >= 0 && row < rows && column < columns && board[row, column] == 0;
    }

    public bool Move(int currentRow, int currentColumn, int currentMoveIndex)
    {
        board[currentRow, currentColumn] = currentMoveIndex;

        if (currentMoveIndex >= maxMoves)
        {
            // solution found
            return true;
        }

        foreach (var move in KNIGHT_MOVES)
        {
            var nextRow = currentRow + move.rowDelta;
            var nextColumn = currentColumn + move.columnDelta;
            if (IsLegalMove(nextRow, nextColumn) && Move(nextRow, nextColumn, currentMoveIndex + 1))
            {
                return true;
            }
        }

        // this move is not a valid one, reset current mark
        board[currentRow, currentColumn] = 0;
        return false;
    }

    public override string ToString()
    {
        var builder = new StringBuilder();
        builder.Append("board:\n");
        for (int row = 0; row < rows; ++row)
        {
            for (int column = 0; column < columns; ++column)
            {
                builder.AppendFormat(" {0, 3}", board[row, column]);
            }
            builder.AppendLine();
        }  
        return builder.ToString();
    }
}

public struct Move
{
    public readonly int rowDelta;
    public readonly int columnDelta;

    public Move(int rowDelta, int columnDelta)
    {
        this.rowDelta = rowDelta;
        this.columnDelta = columnDelta;
    }
}

