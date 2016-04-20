CIVL=civl
VERIFY=$(CIVL) verify

all: arrayPointer arrays assume \
	atomChooseBad atomicBlockedResume \
	atomicStatement atomicWait atomStatement \
	atomWaitBad bigO break bundleArray bundleConcrete \
	bundleSize bundleStruct bundleStructComponent \
	cast choose chooseInt comm compare conditionalExpression \
	continue duffs dynamicStruct emptyWhen exit for functionPrototype \
	implies linkedList malloc mallocBad mallocBad2 \
	mallocBad3 mallocBad4 memcpy minimal nonbooleanCondition \
	null pointers quantifiers scoping self sideEffects sizeof \
	struct structArray structStruct switch

arrayPointer: arrayPointer.cvl
	$(VERIFY) arrayPointer.cvl

arrays: arrays.cvl
	$(VERIFY) arrays.cvl
	
assume: assume.cvl
	$(VERIFY) assume.cvl
	
atomChooseBad: atomChooseBad.cvl
	$(VERIFY) atomChooseBad.cvl

atomicBlockedResume: atomicBlockedResume.cvl
	$(VERIFY) atomicBlockedResume.cvl
	
atomicStatement: atomicStatement.cvl
	$(VERIFY) atomicStatement.cvl -inputB=3
	
atomicWait: atomicWait.cvl
	$(VERIFY) atomicWait.cvl -inputN=3 
	
atomStatement: atomStatement.cvl
	$(VERIFY) atomStatement.cvl
	
atomWaitBad: atomWaitBad.cvl
	$(VERIFY) atomWaitBad.cvl
	
bigO: bigO.cvl
	$(VERIFY) bigO.cvl
	
break: break.cvl
	$(VERIFY) break.cvl
	
bundleArray: bundleArray.cvl
	$(VERIFY) bundleArray.cvl
	
bundleConcrete: bundleConcrete.cvl
	$(VERIFY) bundleConcrete.cvl
	
bundleSize: bundleSize.cvl
	$(VERIFY) bundleSize.cvl
	
bundleStruct: bundleStruct.cvl
	$(VERIFY) bundleStruct.cvl
	
bundleStructComponent: bundleStructComponent.cvl
	$(VERIFY) bundleStructComponent.cvl
	
cast: cast.cvl
	$(VERIFY) cast.cvl
	
choose: choose.cvl
	$(VERIFY) choose.cvl
	
chooseInt: chooseInt.cvl
	$(VERIFY) chooseInt.cvl
	
comm: comm.cvl
	$(VERIFY) comm.cvl
	
compare: compare.cvl
	$(VERIFY) compare.cvl
	
conditionalExpression: conditionalExpression.cvl
	$(VERIFY) conditionalExpression.cvl
	
continue: continue.cvl
	$(VERIFY) continue.cvl
	
duffs: duffs.cvl
	$(VERIFY) duffs.cvl
	
dynamicStruct: dynamicStruct.cvl
	$(VERIFY) dynamicStruct.cvl
	
emptyWhen: emptyWhen.cvl
	$(VERIFY) emptyWhen.cvl
	
exit: exit.cvl
	$(VERIFY) exit.cvl
	
for: for.cvl
	$(VERIFY) for.cvl
	
functionPrototype: functionPrototype.cvl
	$(VERIFY) functionPrototype.cvl

implies: implies.cvl
	$(VERIFY) implies.cvl
	
linkedList: linkedList.cvl
	$(VERIFY) linkedList.cvl
	
malloc: malloc.cvl
	$(VERIFY) malloc.cvl
	
mallocBad: mallocBad.cvl
	$(VERIFY) mallocBad.cvl
	
mallocBad2: mallocBad2.cvl
	$(VERIFY) mallocBad2.cvl
	
mallocBad3: mallocBad3.cvl
	$(VERIFY) mallocBad3.cvl
	
mallocBad4: mallocBad4.cvl
	$(VERIFY) mallocBad4.cvl
	
memcpy: memcpy.cvl
	$(VERIFY) memcpy.cvl
	
minimal: minimal.cvl
	$(VERIFY) minimal.cvl
	
nonbooleanCondition: nonbooleanCondition.cvl
	$(VERIFY) nonbooleanCondition.cvl
	
null: null.cvl
	$(VERIFY) null.cvl
	
pointers: pointers.cvl
	$(VERIFY) pointers.cvl
	
quantifiers: quantifiers.cvl
	$(VERIFY) quantifiers.cvl
	
scoping: scoping.cvl
	$(VERIFY) scoping.cvl
	
self: self.cvl
	$(VERIFY) self.cvl
	
sideEffects: sideEffects.cvl
	$(VERIFY) sideEffects.cvl

sizeof: sizeof.cvl
	$(VERIFY) sizeof.cvl
	
struct: struct.cvl
	$(VERIFY) struct.cvl
	
structArray: structArray.cvl
	$(VERIFY) structArray.cvl
	
structStruct: structStruct.cvl
	$(VERIFY) structStruct.cvl
	
switch: switch.cvl
	$(VERIFY) switch.cvl

clean:
	rm -rf CIVLREP *~

