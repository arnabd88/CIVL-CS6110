CIVL=civl
VERIFY=$(CIVL) verify

all: fib_bench_false fib_bench_longer_false fib_bench_longer_true fib_bench_longest_false fib_bench_longest_true \
fib_bench_true lazy01_false queue_false queue_ok_true reorder_5_false sigma_false singleton_false \
singleton_with-uninit-problems-true stack_false stack_true stateful01_false stateful01_true sync01_true \
twostage_3_false

fib_bench_false: fib_bench_false.c
	$(VERIFY) fib_bench_false.c
	$(CIVL) replay fib_bench_false.c

fib_bench_longer_false: fib_bench_longer_false.c
	$(VERIFY) fib_bench_longer_false.c
	$(CIVL) replay fib_bench_longer_false.c

fib_bench_longer_true: fib_bench_longer_true.c
	$(VERIFY) fib_bench_longer_true.c
	
fib_bench_longest_false: fib_bench_longest_false.c
	$(VERIFY) fib_bench_longest_false.c
	$(CIVL) replay fib_bench_longest_false.c

fib_bench_longest_true: fib_bench_longest_true.c
	$(VERIFY) fib_bench_longest_true.c
	
fib_bench_true: fib_bench_true.c
	$(VERIFY) fib_bench_true.c

lazy01_false: lazy01_false.c
	$(VERIFY) lazy01_false.c
	$(CIVL) replay lazy01_false.c
	
queue_false: queue_false.c
	$(VERIFY) queue_false.c
	$(CIVL) replay queue_false.c

queue_ok_true: queue_ok_true.c
	$(VERIFY) queue_ok_true.c

reorder_5_false: reorder_5_false.c
	$(VERIFY) reorder_5_false.c
	$(CIVL) replay reorder_5_false.c
	
sigma_false: sigma_false.c
	$(VERIFY) sigma_false.c
	$(CIVL) replay sigma_false.c

singleton_false: singleton_false.c
	$(VERIFY) singleton_false.c
	$(CIVL) replay singleton_false.c
	
singleton_with-uninit-problems-true: singleton_with-uninit-problems-true.c
	$(VERIFY) singleton_with-uninit-problems-true.c
	
stack_false: stack_false.c
	$(VERIFY) stack_false.c
	$(CIVL) replay stack_false.c
	
stack_true: stack_true.c
	$(VERIFY) stack_true.c

stateful01_false: stateful01_false.c
	$(VERIFY) stateful01_false.c
	$(CIVL) replay stateful01_false.c
	
stateful01_true: stateful01_true.c
	$(VERIFY) stateful01_true.c
	
sync01_true: sync01_true.c
	$(VERIFY) sync01_true.c

twostage_3_false: twostage_3_false.c
	$(VERIFY) twostage_3_false.c
	$(CIVL) replay twostage_3_false.c

clean:
	rm -rf CIVLREP *~
