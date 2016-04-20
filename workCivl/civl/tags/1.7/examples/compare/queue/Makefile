CIVL=civl
VERIFY=${CIVL} verify

all: twoLock nonblocking

twoLock: driver.cvl queue_two_lock.c
	${VERIFY} driver.cvl queue_two_lock.c

nonblocking: driver.cvl queue_non_blocking.c
	${VERIFY} driver.cvl queue_non_blocking.c

clean: 
	rm -f -r CIVLREP
	rm -r -f *~