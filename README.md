# Conjectural Deductive Programming

This repository provides framework for conjectural deductive programming (CDP), a new strategy for solving classification problems. CDP works by attempting to evolve a set of rules of inference that form a deductive system that can properly classify a given set of data values. Rules of inference are represented as program trees (i.e. Lisp programs), and they can be generated and mutated by the same means that are traditionally used in genetic programming. 

## Usage

The file `main.clj` contains code that uses CDP to attempt to classify the popular Iris Flower dataset. At the moment, attempts at classifying this dataset are largely unsuccessful, unless you only run it with a trivially small number (2-4) of data values. I'm actively working to make the framework more effective at solving this problem, and hopefully others.

To run the code, REPL into the `cdp.main` namespace and run the `iris-evolve` function. `iris-evolve` takes 4 arguments, `steps`, `data-points`, `statement-cap`, and `rule-cap`. The meaning of each of these arguments is explained in the docstring for the function. Sane values for these arguments are 50, 3, 8, and 200, respectively.

## License

MIT License

Copyright (c) 2020 Ella Hoeppner

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.