# agdARGS
Dealing with Flags and Options

I gave a talk about agdARGS in St Andrews on 2015-03-15. The
[slides](https://github.com/gallais/agdARGS/blob/master/doc/2015-03-18-IIM.pdf)
are a good starting point to have an idea of how agdARGS is
implemented. Beware: the terminology varies slightly from the
one now used in the project.

I have implemented two simple examples showcasing the library (flags, options,
arguments parsing and usage):

* [WordCount](https://github.com/gallais/agdARGS/blob/master/agdARGS/Examples/WordCount.agda)
  is a `wc`-like utility,

* and [Sum](https://github.com/gallais/agdARGS/blob/master/agdARGS/Examples/Sum.agda)
  is a simple example of a hierarchical cli: it has two sub-commands ("nat" and "int"
  respectively) which sum the list of numbers (nats and ints respectively) they are
  given.

## Building

This work has been tested using:

* Agda version 2.5.3
* The [standard library](http://github.com/agda/agda-stdlib) version 0.15

To build everything:

```bash
git clone --branch v0.15 http://github.com/agda/agda-stdlib
./agdARGS/all.sh && mv All.agda agdARGS
AGDA_STDLIB=$PWD/agda-stdlib
agda -i . \
     -i $AGDA_STDLIB \
     -c --compile-dir=__build \
     ./agdARGS/All.agda
```

If you already have a copy of the standard library, you can just set
`AGDA_STDLIB` appropriately.
