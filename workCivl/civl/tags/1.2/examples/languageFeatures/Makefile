CIVL=civl
VERIFY=$(CIVL) verify -enablePrintf=false
all: 2dpointerTest abstractFun abstractFunNoArg arrayDefProblem arrayLiteral \
arrayPointer arrays assertNonNullPointer assertNullPointer assertPrintf assignInput \
assignIntWtReal assume atomChooseBad atomicBlockedResume atomicStatement atomicWait \
atomStatement atomWaitBad badGuard bitwise break bundleArray bundleConcrete \
bundleSize bundleStruct bundleTest bundleTestBad cast char choose choose_int \
civlfor civlParfor civlPragma comma compare conditionalExpression continue \
duffs dynamicStruct emptyWhen enum1 enum2 for functionBad functionPointer \
functionPrototype functionPrototypeBad implies include1 include2 include3 \
inputBad int2char int2charBad int2charBad2 int2float intToBool linkedList \
malloc mallocBad mallocBad2 memLeak memoryLeak minimal nonbooleanCondition \
noopBad not null outputBad pointerAdd pointerAdd1 pointerAdd2 pointerAddBad \
pointerAddBad2 pointers pointerSubtraction pointerSubtractionBad pointerSubtractionBad2 pointersBad\
procBound processLeak procNull quantifiers removedHeapPointer scopeOperators \
scoping self sideEffectLoop sideEffects sizeof spawnFoo stringTest struct \
structArray structStruct switch undefHeapPointer undefPointer union 

2dpointerTest: 2dpointerTest.cvl
	$(VERIFY) 2dpointerTest.cvl

abstractFun: abstractFun.cvl
	$(VERIFY) abstractFun.cvl

abstractFunNoArg: abstractFunNoArg.cvl
	$(VERIFY) abstractFunNoArg.cvl

arrayDefProblem: arrayDefProblem.cvl
	$(VERIFY) arrayDefProblem.cvl

arrayLiteral: arrayLiteral.cvl
	$(VERIFY) arrayLiteral.cvl

arrayPointer: arrayPointer.cvl
	$(VERIFY) arrayPointer.cvl

arrays: arrays.cvl
	$(VERIFY) arrays.cvl

assertNonNullPointer: assertNonNullPointer.cvl
	$(VERIFY) assertNonNullPointer.cvl

assertNullPointer: assertNullPointer.cvl
	$(VERIFY) assertNullPointer.cvl

assertPrintf: assertPrintf.cvl
	$(VERIFY) assertPrintf.cvl

assignInput: assignInput.cvl
	$(VERIFY) assignInput.cvl

assignIntWtReal: assignIntWtReal.cvl
	$(VERIFY) assignIntWtReal.cvl

assume: assume.cvl
	$(VERIFY) assume.cvl

atomChooseBad: atomChooseBad.cvl
	$(VERIFY) atomChooseBad.cvl

atomicBlockedResume: atomicBlockedResume.cvl
	$(VERIFY) atomicBlockedResume.cvl

atomicStatement: atomicStatement.cvl
	$(VERIFY) -inputB=3 atomicStatement.cvl

atomicWait: atomicWait.cvl
	$(VERIFY) -inputN=3 atomicWait.cvl

atomStatement: atomStatement.cvl
	$(VERIFY) atomStatement.cvl

atomWaitBad: atomWaitBad.cvl
	$(VERIFY) atomWaitBad.cvl

badGuard: badGuard.cvl
	$(VERIFY) badGuard.cvl

bigO: bigO.cvl
	$(VERIFY) bigO.cvl

bitwise: bitwise.cvl
	$(VERIFY) bitwise.cvl

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

bundleTest: bundleTest.cvl
	$(VERIFY) bundleTest.cvl

bundleTestBad: bundleTestBad.cvl
	$(VERIFY) bundleTestBad.cvl

cast: cast.cvl
	$(VERIFY) cast.cvl

char: char.cvl
	$(VERIFY) char.cvl

choose: choose.cvl
	$(VERIFY) choose.cvl

choose_int: choose_int.cvl
	$(VERIFY) choose_int.cvl

civlfor: civlfor.cvl
	$(VERIFY) civlfor.cvl

civlParfor: civlParfor.cvl
	$(VERIFY) civlParfor.cvl

civlPragma: civlPragma.cvl
	$(VERIFY) -inputNB=5 civlPragma.cvl

comma: comma.cvl
	$(VERIFY) comma.cvl

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

enum1: enum1.cvl
	$(VERIFY) enum1.cvl

enum2: enum2.cvl
	$(VERIFY) enum2.cvl

for: for.cvl
	$(VERIFY) for.cvl

functionBad: functionBad.cvl
	$(VERIFY) functionBad.cvl

functionPointer: functionPointer.cvl
	$(VERIFY) functionPointer.cvl

functionPrototype: functionPrototype.cvl
	$(VERIFY) functionPrototype.cvl

functionPrototypeBad: functionPrototypeBad.cvl
	$(VERIFY) functionPrototypeBad.cvl

implies: implies.cvl
	$(VERIFY) implies.cvl

include1: include1.cvl
	$(VERIFY) include1.cvl

include2: include2.cvl
	$(VERIFY) include2.cvl

include3: include3.cvl
	$(VERIFY) include3.cvl

inputBad: inputBad.cvl
	$(VERIFY) inputBad.cvl

int2char: int2char.cvl
	$(VERIFY) int2char.cvl

int2charBad: int2charBad.cvl
	$(VERIFY) int2charBad.cvl

int2charBad2: int2charBad2.cvl
	$(VERIFY) int2charBad2.cvl

int2float: int2float.cvl
	$(VERIFY) int2float.cvl

intToBool: intToBool.cvl
	$(VERIFY) intToBool.cvl

linkedList: linkedList.cvl
	$(VERIFY) linkedList.cvl

malloc: malloc.cvl
	$(VERIFY) malloc.cvl

mallocBad: mallocBad.cvl
	$(VERIFY) mallocBad.cvl

mallocBad2: mallocBad2.cvl
	$(VERIFY) mallocBad2.cvl

memLeak: memLeak.cvl
	$(VERIFY) memLeak.cvl

memoryLeak: memoryLeak.cvl
	$(VERIFY) memoryLeak.cvl

minimal: minimal.cvl
	$(VERIFY) minimal.cvl

nonbooleanCondition: nonbooleanCondition.cvl
	$(VERIFY) nonbooleanCondition.cvl

noopBad: noopBad.cvl
	$(VERIFY) noopBad.cvl

not: not.cvl
	$(VERIFY) not.cvl

null: null.cvl
	$(VERIFY) null.cvl

outputBad: outputBad.cvl
	$(VERIFY) outputBad.cvl

pointerAdd: pointerAdd.cvl
	$(VERIFY) pointerAdd.cvl

pointerAdd1: pointerAdd1.cvl
	$(VERIFY) pointerAdd1.cvl

pointerAdd2: pointerAdd2.cvl
	$(VERIFY) pointerAdd2.cvl

pointerAddBad: pointerAddBad.cvl
	$(VERIFY) pointerAddBad.cvl

pointerAddBad2: pointerAddBad2.cvl
	$(VERIFY) pointerAddBad2.cvl

pointers: pointers.cvl
	$(VERIFY) pointers.cvl

pointersBad: pointersBad.cvl
	$(VERIFY) -errorBound=10 pointersBad.cvl

pointerSubtraction: pointerSubtraction.cvl
	$(VERIFY) pointerSubtraction.cvl

pointerSubtractionBad: pointerSubtractionBad.cvl
	$(VERIFY) pointerSubtractionBad.cvl

pointerSubtractionBad2: pointerSubtractionBad2.cvl
	$(VERIFY) pointerSubtractionBad2.cvl

procBound: procBound.cvl
	$(VERIFY) -procBound=10 procBound.cvl

processLeak: processLeak.cvl
	$(VERIFY) processLeak.cvl

procNull: procNull.cvl
	$(VERIFY) procNull.cvl

quantifiers: quantifiers.cvl
	$(VERIFY) quantifiers.cvl

removedHeapPointer: removedHeapPointer.cvl
	$(VERIFY) removedHeapPointer.cvl

scopeOperators: scopeOperators.cvl
	$(VERIFY) scopeOperators.cvl

scoping: scoping.cvl
	$(VERIFY) scoping.cvl

self: self.cvl
	$(VERIFY) self.cvl

sideEffectLoop: sideEffectLoop.cvl
	$(VERIFY) sideEffectLoop.cvl

sideEffects: sideEffects.cvl
	$(VERIFY) sideEffects.cvl

sizeof: sizeof.cvl
	$(VERIFY) sizeof.cvl

spawnFoo: spawnFoo.cvl
	$(VERIFY) spawnFoo.cvl

stringTest: stringTest.cvl
	$(VERIFY) stringTest.cvl

struct: struct.cvl
	$(VERIFY) struct.cvl

structArray: structArray.cvl
	$(VERIFY) structArray.cvl

structStruct: structStruct.cvl
	$(VERIFY) structStruct.cvl

switch: switch.cvl
	$(VERIFY) switch.cvl

undefHeapPointer: undefHeapPointer.cvl
	$(VERIFY) undefHeapPointer.cvl

undefPointer: undefPointer.cvl
	$(VERIFY) undefPointer.cvl

union: union.cvl
	$(VERIFY) union.cvl

clean:
	rm -rf CIVLREP *~
