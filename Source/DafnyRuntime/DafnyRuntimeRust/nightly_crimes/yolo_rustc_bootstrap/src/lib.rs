#[proc_macro]
pub fn do_crimes(_: proc_macro::TokenStream) -> proc_macro::TokenStream {
    if !std::env::args_os().any(|arg| arg == "--cfg=yolo_rustc_bootstrap") {
        let mut args = std::env::args_os();
        let status = std::process::Command::new(args.next().unwrap())
            .arg("--cfg=yolo_rustc_bootstrap")
            .args(args)
            .env("RUSTC_BOOTSTRAP", "1")
            .status()
            .unwrap();

        std::process::exit(status.code().unwrap_or(101));
    }

    Default::default()
}
