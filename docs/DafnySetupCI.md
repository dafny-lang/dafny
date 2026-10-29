# Using Dafny in GitHub Actions

Use the [setup-dafny-action](https://github.com/dafny-lang/setup-dafny-action) to install Dafny in your CI workflows.

## Basic Setup

```yaml
- name: "Install Dafny"
  uses: dafny-lang/setup-dafny-action@v1
```

## Specific Version

```yaml
- name: "Install Dafny"
  uses: dafny-lang/setup-dafny-action@v1
  with:
    dafny-version: "4.9.1"
```

## Nightly Build

```yaml
- name: "Install Dafny"
  uses: dafny-lang/setup-dafny-action@v1
  with:
    dafny-version: "nightly-latest"
```

## Build from Source

```yaml
- name: "Install Dafny"
  uses: dafny-lang/setup-dafny-action@v1
  with:
    dafny-version: "4.9.1"
    build-from-source: "branch-name"
```

The action sets `DAFNY_VERSION` environment variable and works on all platforms including macOS.