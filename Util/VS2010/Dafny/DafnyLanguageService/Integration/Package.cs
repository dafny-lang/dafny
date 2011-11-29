using System;
using System.Collections.Generic;
using System.Text;
using System.Runtime.InteropServices;
using Microsoft.VisualStudio.OLE.Interop;
using MPF = Microsoft.VisualStudio.Package;
using System.ComponentModel.Design;

namespace Demo
{
    public class IronyPackage : Microsoft.VisualStudio.Shell.Package, IOleComponent
    {
        uint componentID = 0;
        public IronyPackage()
        {
            ServiceCreatorCallback callback = new ServiceCreatorCallback(
                delegate(IServiceContainer container, Type serviceType)
                {
                    if (typeof(IronyLanguageService) == serviceType)
                    {
                        IronyLanguageService language = new IronyLanguageService();
                        language.SetSite(this);

                        // register for idle time callbacks
                        IOleComponentManager mgr = GetService(typeof(SOleComponentManager)) as IOleComponentManager;
                        if (componentID == 0 && mgr != null)
                        {
                            OLECRINFO[] crinfo = new OLECRINFO[1];
                            crinfo[0].cbSize = (uint)Marshal.SizeOf(typeof(OLECRINFO));
                            crinfo[0].grfcrf = (uint)_OLECRF.olecrfNeedIdleTime |
                                                          (uint)_OLECRF.olecrfNeedPeriodicIdleTime;
                            crinfo[0].grfcadvf = (uint)_OLECADVF.olecadvfModal |
                                                          (uint)_OLECADVF.olecadvfRedrawOff |
                                                          (uint)_OLECADVF.olecadvfWarningsOff;
                            crinfo[0].uIdleTimeInterval = 300;
                            int hr = mgr.FRegisterComponent(this, crinfo, out componentID);
                        }

                        return language;
                    }
                    else
                    {
                        return null;
                    }
                });

            // proffer the LanguageService
            (this as IServiceContainer).AddService(typeof(IronyLanguageService), callback, true);
        }

        protected override void Dispose(bool disposing)
        {
            try
            {
                if (componentID != 0)
                {
                    IOleComponentManager mgr = GetService(typeof(SOleComponentManager)) as IOleComponentManager;
                    if (mgr != null)
                    {
                        mgr.FRevokeComponent(componentID);
                    }
                    componentID = 0;
                }
            }
            finally
            {
                base.Dispose(disposing);
            }
        }

        #region IOleComponent Members
        public int FContinueMessageLoop(uint uReason, IntPtr pvLoopData, MSG[] pMsgPeeked)
        {
            return 1;
        }

        public int FDoIdle(uint grfidlef)
        {
            IronyLanguageService ls = GetService(typeof(IronyLanguageService)) as IronyLanguageService;

            if (ls != null)
            {
                ls.OnIdle((grfidlef & (uint)_OLEIDLEF.oleidlefPeriodic) != 0);
            }

            return 0;
        }

        public int FPreTranslateMessage(MSG[] pMsg)
        {
            return 0;
        }

        public int FQueryTerminate(int fPromptUser)
        {
            return 1;
        }

        public int FReserved1(uint dwReserved, uint message, IntPtr wParam, IntPtr lParam)
        {
            return 1;
        }

        public IntPtr HwndGetWindow(uint dwWhich, uint dwReserved)
        {
            return IntPtr.Zero;
        }

        public void OnActivationChange(IOleComponent pic, int fSameComponent, OLECRINFO[] pcrinfo, int fHostIsActivating, OLECHOSTINFO[] pchostinfo, uint dwReserved)
        {
        }

        public void OnAppActivate(int fActive, uint dwOtherThreadID)
        {
        }

        public void OnEnterState(uint uStateID, int fEnter)
        {
        }

        public void OnLoseActivation()
        {
        }

        public void Terminate()
        {
        }
        #endregion
    }
}