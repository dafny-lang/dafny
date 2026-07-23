# Dafny Dockerfiles

To streamline the dafny language compilation step, these are a series of Dockerfiles with preconfigured environments
for the target language.

## Dafny Base Image

All langauge images use the dafny base image, which supports `dafny verify`. If you wish to just use the dafny
verifier, use this image.

1. Build the base image

```bash
docker build -t dafny-base .
```

The base image **MUST** be named "dafny-base"

2. Run the base image

```bash
docker run --rm dafny-base <dafny args>
```

`docker run --rm dafny-base` is analogous to just running the `dafny` command. See
[Mounting Local Files](#mounting-local-files) for mounting local `.dfy` files for verification and compilation.

## Dafny Language Images

To compile or translate `.dfy` files into a targeted langauge, build the image for the corresponding language.
**Ensure the `dafny-base` image has been built as described in [Dafny Base Image](#dafny-base-image) section or the
build WILL fail.**

Image names (`-t <name>`) ARE able to be named differently, modify the build and run commands accordingly.

**Run:** `docker run --rm <image name> <dafny args>`

### C#

```bash
docker build -t dafny-cs -f cs.dockerfile .
```

This image supports `dafny run`

### Java

```bash
docker build -t dafny-java -f java.dockerfile .
```

### JavaScript

```bash
docker build -t dafny-js -f js.dockerfile .
```

### Python

```bash
docker build -t dafny-py -f py.dockerfile .
```

### Go

```bash
docker build -t dafny-go -f go.dockerfile .
```

### Rust

```bash
docker build -t dafny-rs -f rs.dockerfile .
```

## Mounting Local Files

Docker containers are isolated from the host file system by default. Directories must be intentionally mounted between
the host machine and the container in order for the container to have access to host files, such as `.dfy` files.

To do so add the following flag to the `docker run` command: `-v "/absolute/path/to/dfy/dir:/dafny"`

The full command would look like: `docker run --rm -v "/absolute/path/to/dfy/dir:/dafny" <image name> <dafny args>`

This would be analogous to running the `dafny` tool in the `/absolute/path/to/dfy/dir` directory.

### Example Usage

Given the following file structure:

```
my-project
└── src
    └── main.dfy
readme.md
...
```

To verify `main.dfy` using the dafny base, inside the `my-project` directory run the following command:

```bash
docker run --rm -v "$(pwd)/src:/dafny" dafny-base verify main.dfy
```

Inside the container, the file system looks like the following:

```
/dafny
└── main.dfy
```

and `dafny` executes inside the `/dafny` directory.
