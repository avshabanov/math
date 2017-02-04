using System;
using System.Diagnostics;
using System.Threading;
using System.Threading.Tasks;

namespace Concurrency
{
    public sealed class AsyncTaskDemo
    {
        public static void Demo1()
        {
            var fooService = new FooService();
            var stopwatch = new Stopwatch();
            stopwatch.Start();
            string v = fooService.Foo(1).Result;
            stopwatch.Stop();
            Console.WriteLine("Value = {0}, elapsed = {1}", v, stopwatch.Elapsed);
        }
    }

    public sealed class FooService
    {
        async Task<string> GetSomething(int n)
        {
            return await Task.Run(delegate () {
                Thread.Sleep(100);
                return "a" + n;
            });
        }

        public async Task<string> Foo(int n)
        {
            string n1 = await this.GetSomething(n + 10);
            string n2 = await this.GetSomething(n + 100);

            return n1 + "-" + n2;
        }
    }
}
