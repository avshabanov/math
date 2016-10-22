using System;
using System.Collections.Generic;

namespace Trees
{
    public sealed class TreeConsDemo
    {
        public static void Demo()
        {
            var tree = TreeNode<int>.Create(new [] { 5, 3, 7, 2, 4, 6, 8 }, Comparer<int>.Default);
            Console.WriteLine("tree=\n{0}", TreeSupport.ToPrettyString(tree));
        }
    }
}