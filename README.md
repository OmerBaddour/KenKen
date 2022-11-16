# KenKen

Solvers for [KenKen](https://www.kenkenpuzzle.com/game) using [Z3](https://github.com/z3prover/z3).

# Project Initialization

```
$ git clone https://github.com/OmerBaddour/KenKen.git
$ cd KenKen
$ python -m venv venv_kenken
$ source venv_kenken/bin/activate
$ pip install -r requirements.txt
```

# Usage

```
$ cd KenKen
$ source venv_kenken/bin/activate
```

Find a [program](https://github.com/OmerBaddour/KenKen/tree/main/src/) that's suitable for your use-case, and follow its instructions. In my opinion the most interesting and useful program is [kenken_image_processor.ipynb](https://github.com/OmerBaddour/KenKen/blob/main/src/kenken_image_processor.ipynb), which takes a screenshot of a KenKen puzzle instance as input, parses it, and outputs a solution.
