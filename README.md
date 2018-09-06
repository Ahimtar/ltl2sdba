Overview
========

LTL2sDBA is a tool that translates LTL formulae to semi-deterministic automata.

Requirements
============

The Spot library <https://spot.lrde.epita.fr/> has to be installed. Version 2.4 or higher is required for LTL3sDBA to compile and work properly.

Installation
============
`make` should be enough to compile LTL3sDBA.

Usage
=====
Use `./ltl2sdba -f 'formula to translate'`, for example `./ltl2sdba -f "F(b | GFa)" -p 2`
See `./ltl2sdba -h` for more information.

Known issues
==========

LTL2sDBA is unable to set more than 32 acceptance marks, therefore some larger formulae cannot be translated. This is a limitation of Spot.
