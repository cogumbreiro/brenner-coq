Brenner
=======

Brenner is a calculus for reasoning about task parallelism and barrier synchronization. This calculus distils the semantics of [phasers](http://habanero.rice.edu/) and unifies the synchronisation patterns of various abstractions such as:

* boolean latch
* count-down latch
* cyclic barrier
* futures
* join barriers of the fork/join parallelism
* pipe line synchronisation (*e.g.*, bounded producer-consumer)

We use operational semantics to define the formal meaning of each operation and implement our definitions in Coq.

https://bitbucket.org/cogumbreiro/brenner-coq/src/master/Brenner.v

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