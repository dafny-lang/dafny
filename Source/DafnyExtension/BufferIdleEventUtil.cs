using System;
using System.Collections.Generic;
using System.Windows.Threading;
using Microsoft.VisualStudio.Text;


namespace DafnyLanguage
{

    /// <summary>
    /// Handy reusable utility to listen for change events on the associated buffer, but
    /// only pass these along to a set of listeners when the user stops typing for a half second
    /// </summary>
    static class BufferIdleEventUtil
    {
        static object bufferListenersKey = new object();
        static object bufferTimerKey = new object();

        #region Public interface

        public static bool AddBufferIdleEventListener(ITextBuffer buffer, EventHandler handler)
        {
            HashSet<EventHandler> listenersForBuffer;
            if (!TryGetBufferListeners(buffer, out listenersForBuffer))
                listenersForBuffer = ConnectToBuffer(buffer);

            if (listenersForBuffer.Contains(handler))
                return false;

            listenersForBuffer.Add(handler);

            return true;
        }

        public static bool RemoveBufferIdleEventListener(ITextBuffer buffer, EventHandler handler)
        {
            HashSet<EventHandler> listenersForBuffer;
            if (!TryGetBufferListeners(buffer, out listenersForBuffer))
                return false;

            if (!listenersForBuffer.Contains(handler))
                return false;

            listenersForBuffer.Remove(handler);

            if (listenersForBuffer.Count == 0)
                DisconnectFromBuffer(buffer);

            return true;
        }

        #endregion

        #region Helpers

        static bool TryGetBufferListeners(ITextBuffer buffer, out HashSet<EventHandler> listeners)
        {
            return buffer.Properties.TryGetProperty(bufferListenersKey, out listeners);
        }

        static void ClearBufferListeners(ITextBuffer buffer)
        {
            buffer.Properties.RemoveProperty(bufferListenersKey);
        }

        static bool TryGetBufferTimer(ITextBuffer buffer, out DispatcherTimer timer)
        {
            return buffer.Properties.TryGetProperty(bufferTimerKey, out timer);
        }

        static void ClearBufferTimer(ITextBuffer buffer)
        {
            DispatcherTimer timer;
            if (TryGetBufferTimer(buffer, out timer))
            {
                if (timer != null)
                    timer.Stop();
                buffer.Properties.RemoveProperty(bufferTimerKey);
            }
        }

        static void DisconnectFromBuffer(ITextBuffer buffer)
        {
            buffer.Changed -= BufferChanged;

            ClearBufferListeners(buffer);
            ClearBufferTimer(buffer);

            buffer.Properties.RemoveProperty(bufferListenersKey);
        }

        static HashSet<EventHandler> ConnectToBuffer(ITextBuffer buffer)
        {
            buffer.Changed += BufferChanged;

            RestartTimerForBuffer(buffer);

            HashSet<EventHandler> listenersForBuffer = new HashSet<EventHandler>();
            buffer.Properties[bufferListenersKey] = listenersForBuffer;

            return listenersForBuffer;
        }

        static void RestartTimerForBuffer(ITextBuffer buffer)
        {
            DispatcherTimer timer;

            if (TryGetBufferTimer(buffer, out timer))
            {
                timer.Stop();
            }
            else
            {
                timer = new DispatcherTimer(DispatcherPriority.ApplicationIdle)
                {
                    Interval = TimeSpan.FromMilliseconds(500)
                };

                timer.Tick += (s, e) =>
                {
                    ClearBufferTimer(buffer);

                    HashSet<EventHandler> handlers;
                    if (TryGetBufferListeners(buffer, out handlers))
                    {
                        foreach (var handler in handlers)
                        {
                            handler(buffer, new EventArgs());
                        }
                    }
                };

                buffer.Properties[bufferTimerKey] = timer;
            }

            timer.Start();
        }

        static void BufferChanged(object sender, TextContentChangedEventArgs e)
        {
            ITextBuffer buffer = sender as ITextBuffer;
            if (buffer == null)
                return;

            RestartTimerForBuffer(buffer);
        }

        #endregion
    }

}
