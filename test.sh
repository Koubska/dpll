for i in `seq 1 100`; do
 timeout 10 python3 dpll.py benchmarks/example-$i.cnf ulimit -S -v 4194304
 ./minisat benchmarks/example-$i.cnf
 echo $i
done
