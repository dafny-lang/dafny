using Microsoft.Dafny.LanguageServer.Workspace;
using Xunit;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Synchronization;

public class PublishedVerificationStatusTests {
  [Fact]
  public void CombineTest() {
    Assert.Equal(PublishedVerificationStatus.Running,
      NotificationPublisher.Combine(PublishedVerificationStatus.Stale, PublishedVerificationStatus.Running));
    Assert.Equal(PublishedVerificationStatus.Running,
      NotificationPublisher.Combine(PublishedVerificationStatus.Queued, PublishedVerificationStatus.Running));
    Assert.Equal(PublishedVerificationStatus.Queued,
      NotificationPublisher.Combine(PublishedVerificationStatus.Stale, PublishedVerificationStatus.Queued));
    Assert.Equal(PublishedVerificationStatus.Stale,
      NotificationPublisher.Combine(PublishedVerificationStatus.Stale, PublishedVerificationStatus.Error));
    Assert.Equal(PublishedVerificationStatus.Running,
      NotificationPublisher.Combine(PublishedVerificationStatus.Running, PublishedVerificationStatus.Error));
    Assert.Equal(PublishedVerificationStatus.Running,
      NotificationPublisher.Combine(PublishedVerificationStatus.Running, PublishedVerificationStatus.Correct));
    Assert.Equal(PublishedVerificationStatus.Error,
      NotificationPublisher.Combine(PublishedVerificationStatus.Error, PublishedVerificationStatus.Correct));
  }
}