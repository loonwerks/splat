test-harness/SML
================

The code in this directory supports the creation of a test harness for
a particular filter. It is a hand-worked example on which higher
levels of automation is to be based.

Typing

   Holmake

builds three executables: src, filter, and target. An invocation

   ./src | ./filter | ./target

will generate random messages (byte strings of length 12) in src and
send them through the pipe to the filter process, which will drop
incorrect messages, while sending along the others to the target
process. Helpful messages are printed out by each process as they run.

See src.sml to view the random generation of conforming (and
unconforming) messages. The random generation is constrained in such a
way as to build correct messages, except that every tenth message is
unconstrained and therefore quite likely to not pass the filter.

See filter.sml to see the creation of the filter from a regexp, and its
application. See target.sml to see the collection of the incoming
data.
