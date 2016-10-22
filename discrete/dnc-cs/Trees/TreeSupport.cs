using System;
using System.Collections.Generic;
using System.Text;

namespace Trees
{
    /// <summary>
    /// Represents a node in a binary tree.
    /// </summary>
    public sealed class TreeNode<TValue>
    {
        public TValue Value { get; set; }
        public TreeNode<TValue> Left { get; set; }
        public TreeNode<TValue> Right { get; set; }

        public static TreeNode<T> Insert<T>(TreeNode<T> tree, IComparer<T> comparer, T value)
        {
            for (;;)
            {
                var compareResult = comparer.Compare(tree.Value, value);
                if (compareResult < 0)
                {
                    if (tree.Left == null)
                    {
                        tree.Left = new TreeNode<T> { Value = value };
                        return tree.Left;
                    }

                    tree = tree.Left;
                    continue;
                }
                else if (compareResult > 0)
                {
                    if (tree.Right == null)
                    {
                        tree.Right = new TreeNode<T> { Value = value };
                        return tree.Right;
                    }

                    tree = tree.Right;
                    continue;
                }  

                return tree;
            }
        }

        public static TreeNode<T> Create<T>(IEnumerable<T> values, IComparer<T> comparer)
        {
            TreeNode<T> result = null;

            foreach (T value in values)
            {
                var newNode = new TreeNode<T> { Value = value };
                if (result == null)
                {
                    result = newNode;
                    continue;
                }

                Insert(result, comparer, value);
            }

            return result;
        }
    }

    public abstract class TreeSupport {

        public static string ToPrettyString<T>(TreeNode<T> tree) {
            var sb = new StringBuilder(100);
            AppendPrettyRepresentation(sb, tree, 0);
            return sb.ToString();
        }

        public static void AppendPrettyRepresentation<T>(StringBuilder sb, TreeNode<T> tree, int ident)
        {
            if (tree == null)
            {
                return;
            }
            AppendPrettyRepresentation(sb, tree.Left, ident + 1);
            for (int i = 0; i < ident; ++i)
            {
                sb.Append(' ');
            }
            sb.Append(String.Format("{0}", tree.Value)).Append('\n');
            AppendPrettyRepresentation(sb, tree.Right, ident + 1);
        }
    }
}
