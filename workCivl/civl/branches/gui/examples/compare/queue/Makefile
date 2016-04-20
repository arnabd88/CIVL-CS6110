CIVL=civl
VERIFY=${CIVL} verify -userIncludePath=.
REPLAY=${CIVL} replay -showTransitions

all: twoLock nonblocking

twoLock: driver.cvl queue_two_lock.c
	${VERIFY} -collectOutput=false driver.cvl queue_two_lock.c

nonblocking: driver.cvl queue_non_blocking.c
	${VERIFY} -min -inputN=1 -collectOutput=false driver.cvl queue_non_blocking.c
	${REPLAY} driver.cvl queue_non_blocking.c

clean:
	rm -rf CIVLREP/*
