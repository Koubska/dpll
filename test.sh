for i in `seq 1 100`; do
 echo $i
 time python3 dpll.py benchmarks/example-$i.cnf ulimit -S -v 4194304
 #./minisat benchmarks/example-$i.cnf
done
