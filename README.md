coq-smt-check
=============

This is a simple way to invoke an SMT solver (currently Z3) on Coq goals.
It does *NOT* generate proof objects. It is meant purely for sanity checking
goals.

The main tactic is 'z3 solve' which invokes z3 on the current goal. The
core of the plugin is the conversion from Coq to SMT2 format. At the moment,
the conversion handles the following:

 - boolean connectives, /\, \/, not
 - equality
 - variables
 - real numbers, +, -, /, constants

If your problem fits in this fragment (it can contain other facts as well), then
you can run:

   z3 solve.

If the tactic succees then the solver solved the tactic. If it fails it will
display an error message. To get more information about the problem that was
passed to the smt solver, run 'z3 solve debug'.

See the test-suite directory for examples.

Install from OPAM
-----------------
Make sure you added the [Coq repository](coq.io/opam/):

    opam repo add coq-released https://coq.inria.fr/opam/released

and run:

    opam install coq-smt-check

Contributors
------------

This plugin was started by Vignesh Gowada at UCSD as part of the [VeriDrone](http://veridrone.ucsd.edu/) project. It was updated and is currently maintained by Gregory Malecha.

External contributions are always welcome.