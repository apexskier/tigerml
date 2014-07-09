tigerml
=======

Tiger compiler in ML.

## Language Specifications

Except where otherwise noted, the language this complier applies to conforms to
the one described in Appel's [Modern Compiler Implementation in
ML](https://www.cs.princeton.edu/~appel/modern/ml/).

### Break Statements

Break statements are allowed in the body of for or while loops, except in new
declarations within those bodies.

Breaks apply to their closest parent loop.

### Classes

Classes can contain two types of attributes: class variables, like regular
variables, and methods, like functions. Classes extend a single other class,
inheriting all attributes, and overriding those of the same name implicitly.
The base class is `Object` and has no attributes.

Class variables can call methods declared before them or in parent classes in
their initializations. Class variables cannot be uninitialized.

Methods can access class variables declared before them, lexically.

## Language Design Philosophies

During semantic analysis, I'm going to generally assume the programmer knows
what they are doing.  When typing errors are found, the compiler should go on
as if variables had been declared and expressions result in their proper types
