Due to [cargo issue #1796](https://github.com/rust-lang/cargo/issues/1796), we can not depend on
`serde_json` as a `dev-dependency` in `js_int` without breaking `no_std` compatibility, because
`serde_json` isn't `no_std`-compatible (because of that same cargo bug – see
[serde_json PR #516](https://github.com/serde-rs/json/pull/516)).

Thus, the `serde` tests live in this separate crate.
