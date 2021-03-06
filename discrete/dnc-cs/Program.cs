﻿using System;
using Trees;
using Combinatorics;
using Concurrency;

namespace ConsoleApplication
{
    public class Program
    {
        public static void Main(string[] args)
        {
            Console.WriteLine("== DotNetCore CS Demos ==");
            var mode = "asyncTaskDemo";
            if (args.Length > 1)
            {
                mode = args[1];
            }

            switch (mode)
            {
                case "trees":
                    TreeConsDemo.Demo();
                    break;
                case "longestDictMatch":
                    LongestDictionaryMatch.Demo1();
                    break;
                case "asyncTaskDemo":
                    AsyncTaskDemo.Demo1();
                    break;
                default:
                    Console.WriteLine("Unknown mode {0}", mode);
                    break;
            }
        }
    }
}
