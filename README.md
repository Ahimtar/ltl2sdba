Overview
========

LTL2SDBA is a tool that translates LTL formulae to semi-deterministic automata.

Requirements
============

The Spot library <https://spot.lrde.epita.fr/> has to be installed. Version 2.4 or higher is required for LTL2SDBA to compile and work properly.

Installation
============
`make` should be enough to compile LTL2SDBA.

Usage
=====
Use `./ltl2sdba -f 'formula to translate' -p 2`, for example `./ltl2sdba -f "F(b | GFa)" -p 2`  
See `./ltl2sdba -h` for more information.
