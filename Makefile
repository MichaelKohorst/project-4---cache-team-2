CC=gcc

all: sim.o
	gcc sim.o -o sim 

sim.o: sim.c
	gcc -c sim.c -o sim.o 

clean:
	rm -Rf sim.o sim

