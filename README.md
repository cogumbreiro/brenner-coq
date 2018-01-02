Brenner
=======

The latest version of this project can be found here:

https://gitlab.com/cogumbreiro/brenner-coq

About
=====

Brenner is a calculus for reasoning about task parallelism and barrier synchronization. This calculus distils the semantics of [phasers](http://habanero.rice.edu/) and unifies the synchronisation patterns of various abstractions such as:

* boolean latch
* count-down latch
* cyclic barrier
* futures
* join barriers of the fork/join parallelism
* pipe line and streaming synchronisation (*e.g.*, bounded producer-consumer)

We use operational semantics to define the formal meaning of each operation and implement our definitions in Coq.

Table of contents
=================

 * [Phaser.v](src/Phaser.v) - the phaser abstract data type
 * [PhaserMap.v](src/PhaserMap.v) - the phaser map abstract data type
 * [Syntax.v](src/Syntax.v) - the syntax of Brenner programs
 * [Semantics.v](src/Semantics.v) - the operational semantics of Brenner programs
 * [Vars.v](src/Vars.v) - defines the basic data structures used in the theory (meta-variables, sets, and maps)
 * [Example1.v](src/Example1.v) - a reduction example
 * [ResourceDependency.v](src/ResourceDependency.v) - defines the concurrency dependencies in a Brenner state, defines deadlocked states
 * [Soundness.v](src/Soudness.v) - soundness of the deadlock detection algorithm
 * [Completeness.v](src/Completeness.v) - completenenss of the deadlock detection algorithm

Syntax
======

Tasks are spawned in two steps. First, we create a task name (*tid* short for task identifier).
```
t <- NEW_TID
```
Then we launch the task with fork, where `t` is a task name and `b` is a Brenner program.
```
FORK (t, b)
```
For control flow, we have a non-deterministic loop:
```
LOOP(b)
```

To represent an operation that does not interfere with synchronization we use instruction skip.
```
SKIP
```
Then, we have phaser instructions. Tasks can be registered with a phaser to be able to manipulate it.

Tasks can create phasers dynamically. The tasks creating a phaser is automatically registered with it.
```
p <- NEW_PHASER
```
Registered tasks are assigned a phase, that can be advanced.
```
ADV(p)
```
Registered tasks can also register other tasks.
```
REG(p, t)
```
and deregister themselves
```
DEREG(p)
```
Finally, a task can await for a phase number, which means the task blocks until all register tasks advance their local phases until a certain number. Even unregistered tasks can await on a phaser.
```
AWAIT(p, 10)
```
Alternatively, a registered task can await for other tasks to reach their local phase.
```
AWAIT(p)
```
Programs are composed with a double semi-colon `;;`.

See also:

 * [C implementation of phasers](http://locklessinc.com/articles/phasers/)
 * [Java implementation of phasers](http://docs.oracle.com/javase/7/docs/api/java/util/concurrent/Phaser.html)

Changelog
=========

[Version 1.0](https://bitbucket.org/cogumbreiro/brenner-coq/src/v1.0/):

 * Proved an extended version of the formalism in our
   [PPoPP15 paper](https://bitbucket.org/cogumbreiro/armus/wiki/PPoPP15).

[Version 0.2](https://bitbucket.org/cogumbreiro/brenner-coq/src/v0.2/):

 * Refactored the theory in resource-dependencies into a bipartite
   graph theory. Defined the notion of contracting a bipartite graph and
   showed that whenever there is a cycle in the left-hand-side contracted graph,
   there is a cycle in the right-hand-side contracted graph. Applied this
   theory to GRG/WFG/SG, which means that we have now double implication on
   cycle existence.

[Version 0.1](https://bitbucket.org/cogumbreiro/brenner-coq/src/v0.1/):

 * Proved that a cycle in the WFG implies a cycle in the SG.
 * Created definitions: syntax, operational semantics, resource dependencies.
