
# Build world: opam

_NB: you may need to add `sudo` everywhere_

```shell
# assume your ubuntu is named `cav`
# current folder: /home/cav/CertrBPF
# install the basic tool
apt-get update && apt-get install -y software-properties-common

# install gcc 9.4.0
apt install build-essential

# install gcc lib
apt-get install gcc-multilib

# install llvm
apt-get install -y llvm
apt-get install clang

# install pip3 and pyelftools
apt install python3-pip python3-serial
pip3 install pyelftools

# install opam
add-apt-repository ppa:avsm/ppa
apt update
apt install opam

# install ocaml/coq/compcert etc by opam
opam init
# install ocaml
opam switch create bpf ocaml.4.11.1

eval $(opam env)

opam switch list
#   switch  compiler      description
->  bpf     ocaml.4.11.1  bpf

# install coq, compcert-32, etc. NB we need to keep the build directory of compcert-32 by `-b`
opam repository add coq-released https://coq.inria.fr/opam/released

# install coq and coqide
opam install coq.8.13.2 coqide.8.13.2 coq-elpi.1.11.0
opam install -b coq-compcert-32.3.9
opam install coq-vst-32.2.8

# install coq2html
git clone https://github.com/xavierleroy/coq2html.git
cd coq2html
make coq2html

# set path variables & add COQPATH
apt-get install vim
# 1) find . -name ".opam" -type d
#  ==> ./home/cav/.opam
# 2); adding the line: `export PATH=$PATH:/home/cav/.opam/bpf/bin:/home/cav/CertrBPF/coq2html`
# 3); adding the line `export COQPATH="$(opam var lib)/coq-variant/compcert32"`
vim /home/cav/.bashrc
source /home/cav/.bashrc
```

# Build dx
```shell
# current folder: /home/cav/CertrBPF
# install dx
git clone --branch compcert-3.9 https://gitlab.univ-lille.fr/samuel.hym/dx.git
cd dx
./configure --cprinterdir="$(opam var lib)/dx" --compcertdir="$(opam var coq-compcert-32:build)" --install-compcert-printer
make all install
```
# Build CertrBPF
```shell
# current folder: /home/cav/CertrBPF/dx
# install CertrBPF
cd ..
git clone --branch CAV22-AE https://gitlab.inria.fr/syuan/rbpf-dx.git
cd rbpf-dx

# modify the file `_CoqProject`:
# -R /home/shyuan/.opam/4.11.1/lib/coq-variant/compcert32/compcert compcert
# ===>
# -R /home/cav/.opam/bpf/lib/coq-variant/compcert32/compcert compcert
vim _CoqProject

# modify the file `Makefile.config` and `verifier/Makefile.config`:
# OPAMPREFIX := /home/shyuan/.opam/4.11.1
# ===>
# OPAMPREFIX := /home/cav/.opam/bpf
vim Makefile.config
vim verifier/Makefile.config

make all
```
# Test CertrBPF 
```shell
# current folder: /home/cav/CertrBPF/rbpf-dx
# Here, we only test the native board (*You could reproduce the same result in the paper if you have the same physical boards: Nordic nRF52840 development kit, the Espressif WROOM-32 board, and the Sipeed Longan Nano GD32VF103CBT6 development board*)

# test bench_bpf_coq_incr
# compile CertBPF
make -C benchmark_data/bench_bpf_coq_incr/bpf
make -C benchmark_data/bench_bpf_coq_incr
# run on a native board using CertBPF
make -C benchmark_data/bench_bpf_coq_incr term
# complie original rBPF: Vanilla-rBPF
make -C benchmark_data/bench_bpf_coq_incr BPF_COQ=0 BPF_USE_JUMPTABLE=0
make -C benchmark_data/bench_bpf_coq_incr BPF_COQ=0 BPF_USE_JUMPTABLE=0 term

# test bench_bpf_coq_unit
# compile CertBPF
make -C benchmark_data/bench_bpf_coq_unit
make -C benchmark_data/bench_bpf_coq_unit term
# complie original rBPF: Vanilla-rBPF
make -C benchmark_data/bench_bpf_coq_unit BPF_COQ=0 BPF_USE_JUMPTABLE=0
make -C benchmark_data/bench_bpf_coq_unit BPF_COQ=0 BPF_USE_JUMPTABLE=0 term
```

Please don't hesitate to contact [me](https://shenghaoyuan.github.io/)
