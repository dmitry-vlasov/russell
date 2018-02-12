
Russell logical framework
================================

mdl is the implementation of Russell logical framework.
This is a language for pure mathematics, build upon a [Metamath](http://www.metamath.org)
language as a high level superstructure. mdl will support fully automatic proving
facility.

In fact, mdl program is a compiler from a relativily high-level language for the 
representation of formal mathematics to the simple and robust for checking
language Metamath.

The package contains folowing programs:
 * mdl      : the mdl prover and the compiler from russell language to Metamath.
 * mm       : the Metamath translator to smm.
 * metamath : original Metamath checker.
 * smm      : the verifier and translator from smm to russell (simplified Metamath)

Dependencies
------------
mdl uses some boost libraries: spirit, string algos, filesystem. To be sure all of these
are avaliable, install libboost-all-dev (linux). Also Intel Threading Building Blocks (tbb) library
is used, libtbb-dev (Ubuntu). 

Building and translation tests
------------------------------
To make a complete local build and run translation test just execute ./run script.
Math libraries, transleted to smm and Russell will be inside math/tmp directory


 

