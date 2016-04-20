CIVL=civl
VERIFY=${CIVL} verify -enablePrintf=false
REPLAY=${CIVL} replay

all: adder adderBad bank barrier barrier2 barrierBad blockAdder \
blockAdderBad boundedBuffer boundedBuffer_bad dining diningBad dlqueue \
exitBarrier hybrid locksBad locksBad10 locksGood mpi-pthreads readerWriter \
ring ring1 ring1Bad ring2 ring2Bad ring3 ring3Bad spawn spawn2 spawnBad \
two_lock_queue waitSelf wildcard wildcardBad 

adder: adder.cvl
	$(VERIFY) -inputB=5 adder.cvl

adderBad: adderBad.cvl
	$(VERIFY) -inputB=4 -min adderBad.cvl
	$(REPLAY) adderBad.cvl

bank: bank.cvl
	$(VERIFY) -inputNUM_ACCOUNTS=3 bank.cvl

barrier: barrier.cvl
	${VERIFY} -inputB=6 barrier.cvl

barrier2: barrier2.cvl
	$(VERIFY) -inputB=4 barrier2.cvl

barrierBad: barrierBad.cvl
	$(VERIFY) -inputB=4 -min barrierBad.cvl 
	$(REPLAY) -id=0 barrierBad.cvl 

blockAdder: blockAdder.cvl
	$(VERIFY) -inputB=6 -inputW=3 blockAdder.cvl

blockAdderBad: blockAdderBad.cvl
	$(VERIFY) -inputB=6 -inputW=3 -min blockAdderBad.cvl
	$(REPLAY) blockAdderBad.cvl

boundedBuffer: boundedBuffer.cvl
	${VERIFY} boundedBuffer.cvl

boundedBuffer_bad: boundedBuffer_bad.cvl
	${VERIFY} -min boundedBuffer_bad.cvl
	${REPLAY} boundedBuffer_bad.cvl

dining: dining.cvl
	${VERIFY} dining.cvl

diningBad: diningBad.cvl
	${VERIFY} -min diningBad.cvl
	${REPLAY} diningBad.cvl

dlqueue: dlqueue.cvl
	$(VERIFY) dlqueue.cvl

exitBarrier: exitBarrier.cvl
	$(VERIFY) exitBarrier.cvl

hybrid: hybrid.cvl
	$(VERIFY) -inputNPROCS=2 hybrid.cvl

locksBad: locksBad.cvl
	$(VERIFY) locksBad.cvl

locksBad10: locksBad10.cvl
	$(VERIFY) locksBad10.cvl

locksGood: locksGood.cvl
	$(VERIFY) locksGood.cvl

mpi-pthreads: mpi-pthreads.cvl
	$(VERIFY) mpi-pthreads.cvl

readerWriter: readerWriter.cvl
	$(VERIFY) readerWriter.cvl

ring: ring.cvl mp_root.cvh mp_proc.cvh
	$(VERIFY) -deadlock=potential -inputNPROCS_BOUND=10 -inputN_BOUND=5 ring.cvl

ring1: ring1.cvl mp_root.cvh mp_proc.cvh
	$(VERIFY) -deadlock=potential -inputNPROCS=3 ring1.cvl

ring1Bad: ring1Bad.cvl mp_root.cvh mp_proc.cvh
	$(VERIFY) -deadlock=potential -inputNPROCS=3 ring1Bad.cvl

ring2: ring2.cvl mp_root2.cvh mp_proc2.cvh
	$(VERIFY) -inputNPROCS=3 -deadlock=potential ring2.cvl

ring2Bad: ring2Bad.cvl mp_root.cvh mp_proc.cvh
	$(VERIFY) -inputNPROCS=3 -deadlock=potential ring2Bad.cvl

ring3: ring3.cvl
	$(VERIFY) -deadlock=potential ring3.cvl

ring3Bad: ring3Bad.cvl
	$(VERIFY) -deadlock=potential ring3Bad.cvl

spawn: spawn.cvl
	$(VERIFY) -inputN=10 spawn.cvl

spawn2: spawn2.cvl
	$(VERIFY) -inputN=10 spawn2.cvl

spawnBad: spawnBad.cvl
	$(VERIFY) -inputN=10 spawnBad.cvl

two_lock_queue: two_lock_queue.cvl
	$(VERIFY) two_lock_queue.cvl

waitSelf: waitSelf.cvl
	$(VERIFY) waitSelf.cvl

wildcard: wildcard.cvl
	$(VERIFY) wildcard.cvl

wildcardBad: wildcardBad.c
	$(VERIFY) wildcardBad.c
