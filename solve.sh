#!/bin/sh

##### Python
echo "Python pypy3"
pypy3 dpll.py $*
echo "Python python3" 
python3 dpll.py $*
