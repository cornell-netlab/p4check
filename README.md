# P4Check 16

_P4Check 16_ is a _prototype_ implementation of the `P4Check` tool
(for P4 14) described in [our
ECOOP paper](http://dx.doi.org/10.4230/LIPIcs.ECOOP.2019.12).

P4Check is a static checker that eliminates references to invalid headers. 

## Building

+ Install `opam`. Then run `opam install dune`
+ Install dependencies indicated by the command
```
dune external-lib-deps --missing @all
```
For example `opam install core`. 

**N.B.** To install `petr4`, follow the instructions
[here](https://github.com/cornell-netlab/petr4). However, you must run
`git checkout 0.1.1` first, so that you build the most recent release
version and not the development version.

+ Now you can build by running

```
make
```

which will produce an executable in `./p4check`. You may need to run
`chmod +x ./p4check` to provide it with executable permissions.

## Examples

The following examples demonstrate the few important messages that p4check outputs 

### Passing P4 code 

The following example, taken from the P4 Developer Day Tutorials should pass the typechecker.

```
./p4check examples/basic.p4 -I examples/includes
```

### Failing P4 Code

The following modified example should complain about an invalid `ipv4` instance

```
./p4check examples/basic_ipv4bug.p4 -I examples/includes
```

### P4Check Warnings

The following command produces a warning that should be used to guide implementation of the controller

```
./p4check examples/basic_warningipv4.p4 -I examples/includes
```

### Stress Testing

Running the following command shows the limits of our current
implementation. The following is a cross-compiled version of
[`switch.p4`](https://github.com/p4lang/switch) using Barefoot
Networks' `p4_14_to_p4_16` compiler.

```
./p4check ./examples/open_switch.p4
```

If you want to observe the massive size of the types as the program is processed, run

```
./p4check -v ./examples/open_switch.p4
```
