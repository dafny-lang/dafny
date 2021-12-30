using System;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.Util;
using Microsoft.VisualStudio.TestTools.UnitTesting;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Util;

[TestClass]
public class AsyncExtensionsTest {
  [TestMethod]
  public async Task FirstCompletedTaskIsReturned() {
    var one = new TaskCompletionSource<int>();
    var two = new TaskCompletionSource<int>();
    var three = new TaskCompletionSource<int>();
    var resultTask = AsyncExtensions.FirstSuccessfulAsync(one.Task, two.Task, three.Task);
    two.SetResult(2);
    one.SetResult(1);
    three.SetResult(3);
    Assert.AreEqual(2, await resultTask);
  }

  [TestMethod]
  public async Task FirstPassedTaskIsReturnedIfMultipleAreAlreadyCompleted() {
    var one = new TaskCompletionSource<int>();
    var two = Task.FromResult(2);
    var three = Task.FromResult(3);
    var resultTask = AsyncExtensions.FirstSuccessfulAsync(one.Task, two, three);
    one.SetResult(1);
    Assert.AreEqual(2, await resultTask);
  }

  [TestMethod]
  public async Task ReturnsCancelledIfNoneSucceededAndAtLeastOneCancelled() {
    await Assert.ThrowsExceptionAsync<TaskCanceledException>(() => {
      var one = Task.FromException<int>(new Exception());
      var cancellationTokenSource = new CancellationTokenSource();
      cancellationTokenSource.Cancel();
      var two = Task.FromCanceled<int>(cancellationTokenSource.Token);
      var three = Task.FromException<int>(new Exception());
      return AsyncExtensions.FirstSuccessfulAsync(one, two, three);
    });
  }

  [TestMethod]
  public async Task ReturnsAllExceptions() {
    var exception1 = new Exception();
    var exception2 = new Exception();
    try {
      var one = Task.FromException<int>(exception1);
      var two = Task.FromException<int>(exception2);
      await AsyncExtensions.FirstSuccessfulAsync(one, two);
    } catch (AggregateException e) {
      Assert.AreSame(exception1, e.InnerExceptions[0]);
      Assert.AreSame(exception2, e.InnerExceptions[1]);
    }
  }
}