CIVL=civl
VERIFY=${CIVL} verify -userIncludePath=.

all: twoLock nonblocking

twoLock: driver.cvl queue_two_lock.c
	${VERIFY} -collectOutput=false driver.cvl queue_two_lock.c

nonblocking: driver.cvl queue_non_blocking.c
	${VERIFY} -collectOutput=false -showTransitions driver.cvl queue_non_blocking.c

clean:
	rm -rf CIVLREP/*
