
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
mdl uses some boost libraries: spirit, string algos, filesystem.

Building
--------
To build russell environment the boost jam builder is required.
Run:
 1. to build optimized version:  `bjam release -j 4 toolset=gcc`
 2. to build the debug version:  `bjam debug -j 4 toolset=gcc`

Translation tests
-----------------
Scripts 'translate' and 'translate_deep', runs some chains of translations and verifications.
 1. First, checkout the original Metamath source from [math](https://github.com/dmitry-vlasov/math)
repository. 
 2. Then write the correct paths to the binary dir and to the mathematics source dir in
the `config` file. 
 3. Finally, to run test do: `translate uset-100000` (without extension!).
 4. To add valgrind memcheck add the `memcheck` option to the command (as the last parameter).

 

