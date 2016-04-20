CIVL=civl
VERIFY=$(CIVL) verify
REPLAY=$(CIVL) replay

all: queue_false queue_ok_true \
	stack_false stack_true \
	stateful01_false stateful01_true sync01_true
	
queue_false: queue_false.cvl
	$(VERIFY) queue_false.cvl -enablePrintf=false -min
	$(REPLAY) queue_false.cvl
	
queue_ok_true: queue_ok_true.cvl
	$(VERIFY) queue_ok_true.cvl
	
stack_false: stack_false.cvl
	$(VERIFY) -inputSIZE=8 stack_false.cvl -min
	$(REPLAY) stack_false.cvl
	
stack_true: stack_true.cvl
	$(VERIFY) -inputSIZE=8  stack_true.cvl
	
stateful01_false: stateful01_false.cvl
	$(VERIFY) stateful01_false.cvl -min
	$(REPLAY) stateful01_false.cvl

stateful01_true: stateful01_true.cvl
	$(VERIFY) stateful01_true.cvl
	
sync01_true: sync01_true.cvl
	$(VERIFY) sync01_true.cvl
