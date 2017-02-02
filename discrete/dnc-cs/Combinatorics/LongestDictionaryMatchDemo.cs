using System;
using System.Collections.Generic;

namespace Combinatorics
{
    public static class LongestDictionaryMatch
    {
        public static void Demo1()
        {
            Console.WriteLine("LongestDictionaryMatch.Demo1");
            MatchWordToTerm("xyz", "xz");
            MatchWordToTerm("xyz", "xzyyyy");
            MatchWordToTerm("xyykxz", "xz");
        }

        public static void MatchWordToTerm(string word, string term)
        {
            var termMatcher = new TermMatcher(term: term, word: word);
            termMatcher.Match(0, 0);
            if (termMatcher.MatchResult == null)
            {
                Console.WriteLine("Word {0} does not match term {1}", word, term);
                return;
            }

            Console.WriteLine("Word {0} matches term {1} with remove indices=[{2}]", 
                word, term, string.Join(", ", termMatcher.MatchResult));
        }
    }

    sealed class TermMatcher
    {
        readonly string term;
        readonly string word;
        IList<int> result = null;
        readonly List<int> matchPositions = new List<int>();

        public IList<int> MatchResult
        {
            get { return this.result; }
        }

        public TermMatcher(string term, string word)
        {
            this.term = term;
            this.word = word;
        }

        public void Match(int termIndex, int wordIndex)
        {
            //Console.WriteLine(" [DBG] termIndex = {0}, wordIndex = {1}", termIndex, wordIndex);

            if (wordIndex == word.Length)
            {
                if (termIndex < term.Length)
                {
                    // no match
                    return;
                }

                // match found
                if (result == null || result.Count > matchPositions.Count)
                {
                    result = new List<int>(matchPositions);
                }
                return;
            }

            if (result != null && result.Count > matchPositions.Count)
            {
                // heuristic: we already found a match and current search is not good enough
                return;
            }

            if (termIndex < term.Length)
            {
                var wordCh = this.word[wordIndex];
                var termCh = this.term[termIndex];

                if (wordCh == termCh)
                {
                    // first option: add w/ matching result
                    this.Match(termIndex + 1, wordIndex + 1);
                }
            }

            // second option: skip non-matching (or even matching) letter in hope to find
            // match later
            this.matchPositions.Add(wordIndex);
            this.Match(termIndex, wordIndex + 1);
            this.matchPositions.RemoveAt(this.matchPositions.Count - 1);
        }
    }
}
