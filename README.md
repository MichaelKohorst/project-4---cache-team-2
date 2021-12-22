# cisc340-project3-cache-template
Instructions: To run our program, make sure you are in the project directory. Type make clean, enter, type make, enter. This will set up the simulator file to be run. You can then enter for example ./sim -i tests/class.mc That will run the program will the supplied instructions. You can interchange class.mc with any other test we have provided inside the test folder.

sim.c: This is the c code we have written to run machine code and print the output to the command line. It will show the state of each register and memory location after operations are ran from the machine code using input from our tests. But it runs the code pipelines so that multiple instruction will be worked on at once.

Makefile: Allow us to run the sim.c as it runs given commands of the file.

test/
class.asm: This is the supplied assembly language code that can be built into runnable machine code.

class.mc: This is the supplied machine code that can be run by the simulator

Test1.asm: Assembly code for Test 1.

Test1.mc: This code is meant to test the simulator ability to deal with a cache rotations within a single set assuming that the block size is <=4 and nset is 2 and associativity is 2 or 4. It test to see if it will dectect a hit.

Test2.asm: Assembly code for Test 2. 

Test2.asm: This code is meant to test the simulators ability to deal with writing back to memory and  and cycling out the block then coming back to the block and seeing if the block is updated when brought back. This test can also be used to test direct mapping and fully associative caches, with everything in between  
