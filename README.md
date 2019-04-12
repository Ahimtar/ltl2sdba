Overview
========

LTL2SDBA is a tool that translates LTL formulae to semi-deterministic automata via very weak alternating automata and is based on the LTL3TELA tool.

Requirements
============

The Spot library <https://spot.lrde.epita.fr/> has to be installed. Version 2.4 or higher is required for LTL2SDBA to compile and work properly.
G++ version 5.2 or higher is required.

Installation
============
Use the `make` command to compile LTL2SDBA.

Usage
=====
Use `./ltl2sdba -f 'formula to translate'`, for example `./ltl2sdba -f "F(b | GFa)"`
See `./ltl2sdba -h` for options and more information.


If you are a developer and you aim to use this tool somehow, I recommend you to contact me directly first to help you get started faster!
