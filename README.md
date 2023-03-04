# Compiler-JFTT
 A pthon/ply compiler for a simple custom programming language, made for JFTT course.

## Requirements
 - python 3.5+
 - ply module

 ## Files
 - `precompileyacc.py` - replaces binary operations of two numbers with their result
 - `compilerflex.py` - seperates the input code into tokens
 - `compile.py` - contains the main functionality, runs the aformentioned code and interprets the tokens into machine code using ply.yacc module
 
 ## How to run:
  python3 compile.py [input file name] [output file name]