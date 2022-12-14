# Middleware 2022 Femto-Container artifact

This repository contains the artifact for the paper published at [ACM Middleware 2022]
on "Femto-Containers: Lightweight Virtualization and Fault Isolation For Small
Software Functions on Low-Power IoT Microcontrollers", for which you can also check out the [preprint] in PDF.

## Directory overview

**RIOT**: contains the fork of the RIOT source tree that was used for the
measurements. It includes the old rBPF code. It is used to compile the examples
with.

**Femto-Containers**: contains the pure Femto-Containers source code.

**Snippets**: contains the Femto-Containers application snippets used in the
paper submission.

**verified**: contains the CertFC code and proofs.

**examples**: contains a number of full working examples demonstrating
Femto-Containers including an example of over the air updateable Femto-Container
instances.

## How to view this artifact

The main part of this artifact consists of the examples in the `examples`
directory. These can be used to demonstrate the Femto-Container runtime and to
reproduce measurments from the [Middlerware 2022] paper submission.

### Requirements to run the artifacts

To compile the artifacts, an environment able to compile the RIOT operating
system on Linux is required. A Debian-based Linux distribution is recommended.
Furthermore the following tools are required:

* Essential system development tools (GNU Make GCC, standard C library headers),
  can usually be installed by installing `build-essential` on Debian and
  derivatives.
* git
* GDB in the multiarch variant (alternatively: install for each architecture you target the
  corresponding GDB package)
* unzip or p7zip
* wget or curl
* python3
* pyserial (linux distro package often named python3-serial or py3-serial)

These can be installed on Debian and Ubuntu via

```Console
# apt install gcc-multilib build-essential git llvm clang python3 python3-pip wget curl unzip
```

For compiling Femto-Container applications and updating them over the air,
the following is required:

* LLVM and Clang
* python3
* pip
* [pyelftools](https://github.com/eliben/pyelftools)
* [cbor2](https://pypi.org/project/cbor2/)
* [cryptography](https://pypi.org/project/cryptography/)
* [aiocoap](https://pypi.org/project/aiocoap/)
* [linkheader](https://pypi.org/project/linkheader/)

These last four can be installed via Pip using

```Console
$ pip install --user pyelftools cbor2 cryptography aiocoap[all] linkheader
```

### Examples

#### Suit Femtocontainer

The `suit_femtocontainer example contains functionality to run and update
Femto-Container runtimes on a RIOT instance. See the 
[suit_femtocontainer README](https://github.com/future-proof-iot/middleware2022-femtocontainers/blob/main/examples/suit_femtocontainer/README.md)
for details on how to work with this example.

#### Bench BPF Unit

The `bench_bpf_unit` example is a unit test for the different eBPF instructions
that can be run on the different runtimes. The README.md with the example has
additional details on how to compile and what output is expected.

### CertFC

The CertFC with the accompanying benchmark tests are in the `verified` directory.
Installation instructions are provided separately in the [INSTALL.md] file and
details provide in the README.md file in the `verified` directory.

[ACM Middleware 2022]: https://middleware-conf.github.io/2022/
[INSTALL.md]: https://github.com/future-proof-iot/middleware2022-femtocontainers/blob/main/verified/INSTALL.md
[preprint]: https://arxiv.org/pdf/2210.03432.pdf
