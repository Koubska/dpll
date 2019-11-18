for i in `seq 1 100`; do i
 time pypy3 dpll.py benchmarks/example-$i.cnf ulimit -S -v 4194304
 echo $i
done
