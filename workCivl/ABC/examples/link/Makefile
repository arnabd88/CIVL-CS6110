
# a: illustration of crazy linking rules allowed by C,
# resulting in non-typesafe whole program without any
# casts.
a: a0.c a1.c a2.c
	cc -o a a0.c a1.c a2.c

clean:
	rm -f a
