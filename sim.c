#include <errno.h>
#include <ctype.h>
#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <math.h>

#define NUMMEMORY 65536 /* maximum number of data words in memory */
#define NUMREGS 8 /* number of machine registers */

#define ADD 0
#define NAND 1
#define LW 2
#define SW 3
#define BEQ 4
#define JALR 5
#define HALT 6
#define NOOP 7

#define NOOPINSTRUCTION 0x1c00000

typedef struct stateStruct {
	int pc;
	int mem[NUMMEMORY];
	int reg[NUMREGS];
	int numMemory;
	int hits;
	int misses;
} stateType;

typedef struct blockStruct {//struct for block
	int valid;//
	int dirty;//dirty bit
	int line;//line bit
	int tag;//tag bit
	int lru;//lru bit
	int* blockData;//holds the data of the block
} block;


/*
* Log the specifics of each cache action.
*
* address is the starting word address of the range of data being transferred.
* size is the size of the range of data being transferred.
* type specifies the source and destination of the data being transferred.
*
* cache_to_processor: reading data from the cache to the processor
* processor_to_cache: writing data from the processor to the cache
* memory_to_cache: reading data from the memory to the cache
* cache_to_memory: evicting cache data by writing it to the memory
* cache_to_nowhere: evicting cache data by throwing it away
*/
enum action_type {cache_to_processor, processor_to_cache, memory_to_cache, cache_to_memory, cache_to_nowhere};
//print_action(state->pc, blockSize, cache_to_processor);
//print_action(state->pc, blockSize, processor_to_cache);
//print_action(state->pc, blockSize, memory_to_cache);
//print_action(state->pc, blockSize, cache_to_memory);
//print_action(state->pc, blockSize, cache_to_nowhere);
void print_action(int address, int size, enum action_type type)
{
	printf("transferring word [%i-%i] ", address, address + size - 1);
	if (type == cache_to_processor) {
		printf("from the cache to the processor\n");
	} else if (type == processor_to_cache) {
		printf("from the processor to the cache\n");
	} else if (type == memory_to_cache) {
		printf("from the memory to the cache\n");
	} else if (type == cache_to_memory) {
		printf("from the cache to the memory\n");
	} else if (type == cache_to_nowhere) {
		printf("from the cache to nowhere\n");
	}
}

int field0(int instruction){
	return( (instruction>>19) & 0x7);
}

int field1(int instruction){
	return( (instruction>>16) & 0x7);
}

int field2(int instruction){
	return(instruction & 0xFFFF);
}

int opcode(int instruction){
	return(instruction>>22);
}


void printState(stateType *statePtr){
	int i;
	printf("\n@@@\nstate:\n");
	printf("\tpc %d\n", statePtr->pc);
	printf("\tmemory:\n");
	for(i = 0; i < statePtr->numMemory; i++){
		printf("\t\tmem[%d]=%d\n", i, statePtr->mem[i]);
	}	
	printf("\tregisters:\n");
	for(i = 0; i < NUMREGS; i++){
		printf("\t\treg[%d]=%d\n", i, statePtr->reg[i]);
	}
	printf("end state\n");
}

int signExtend(int num){
	// convert a 16-bit number into a 32-bit integer
	if (num & (1<<15) ) {
		num -= (1<<16);
	}
	return num;
}

void print_stats(stateType* state){
        printf("Hits: %d\n", state->hits);
        printf("Misses: %d\n", state->misses);
}

int blockField(int loc, int blockOffset)//this grab the block field of a number
{
	int targetSection = 0;
	int power = 1;
	for(int i = 0; i < blockOffset; i++)//grab the bits that match the block section
	{
		targetSection = targetSection + power;
		power = power *2;
	}
	return targetSection & loc;
}

int lineField(int loc, int lineOffset, int blockOffset)//this grab the line field of a number
{
	int result = 0;
	int targetSection = 0;
	int power = 1;
	for(int i = blockOffset; i < blockOffset + lineOffset; i++)
	{
		targetSection = targetSection + power;//grab the number of bits
		power = power *2;
	}
	result = (targetSection<<blockOffset) & loc;//then shift the bit to the right portion
	return (result>>(blockOffset));//shift back down 

}

int tagField(int loc, int lineOffset, int blockOffset)//this grab the tag field of a number
{
	int result = 0;
	int targetSection = 0;
	int power = 1;
	for(int i = 0; i < blockOffset + lineOffset; i++)//block + offset field is what we do not want so grab it then reverse it.
	{
		targetSection = targetSection + power;
		power = power *2;
	}
	result = (~targetSection) & loc;//inverse
	return (result>>(blockOffset+lineOffset));//shift back down

}

void updateLRU(block** cache, int line, int bound, int width)//runs through and increments all of the blocks have lru's less then this block
{
	for(int i = 0;i < width; i++)
	{
		if(cache[line][i].lru < bound)//Only update those lower than current lru
		{
			cache[line][i].lru = cache[line][i].lru+1;//increment
		}
	}
}

int startOfCacheBlk(block** cache, stateType* state , int x, int y,  int lineOffset, int blockOffset)//grabs the start of block given any position in the block
{
	int result = 0;
	result = cache[y][x].tag<<(lineOffset + blockOffset);//reconstruct the old memory address start.
	result = result + (cache[y][x].line<<blockOffset);//bit shift back and now the block portion is zero
	return result;
}

void writeBack(block** cache, stateType* state , int x, int y, int lineOffset, int blockOffset, int width)//This function writes back to memory
{
	int shift = 1<<blockOffset;
	print_action(startOfCacheBlk(cache, state, x, y,  lineOffset, blockOffset), shift, cache_to_memory);
	int start = startOfCacheBlk(cache, state , x, y, lineOffset, blockOffset);//grab start of cache blk
	for(int i = 0; i < width; i++)
	{
		state->mem[start+i] = cache[y][x].blockData[i];//Then go through cache block updating values
	}
}


int hitCheck(block** cache, int loc, int lineOffset, int blockOffset, int width)//checks to see if the memory has already been load into cache if so then return the set number its in
{
	int result = -1;
	int line = lineField(loc, lineOffset, blockOffset);//grab line portion
	int tagC = tagField(loc, lineOffset, blockOffset);//grab tag portion
	for(int i = 0; i < width; i++)
	{
		if(cache[line][i].valid == 1 && cache[line][i].tag == tagC)//has to be valid and tags must match
		{
			result = i;
		}
	}
	return result;
}

int findValidSpot(stateType* state, block** cache, int loc, int lineOffset, int blockOffset, int blockSize, int width)// width is associativity and finds a valid spot either empty or lru
{
	int result = 0;
	int blockC = blockField(loc, blockOffset);//These grab the current fields
	int lineC = lineField(loc, lineOffset, blockOffset);
	int tagC = tagField(loc, lineOffset, blockOffset);
	int bound = 0;
	int startOfBlk = 0;
	int done = 0;
	int lruLoc = 0;
	for(int i = 0; i < width; i++)//either we will find a valid spot to put the new block in or we will find the one with the lru
	{
		if(cache[lineC][i].valid == 0)//found an open spot
		{
			cache[lineC][i].valid = 1;
			cache[lineC][i].line = lineC;
			cache[lineC][i].tag = tagC;
			cache[lineC][i].dirty = 0;
			bound = cache[lineC][i].lru;
			updateLRU(cache, lineC, bound, width);			
			cache[lineC][i].lru = 0;
			startOfBlk = loc - blockC;
			for(int j = 0; j < blockSize; j++)//Run through all of the sets
			{
				cache[lineC][i].blockData[j] = state->mem[startOfBlk + j];		
			}
			done = 1;//No need to overwrite
			
			result = i;
			i = width;
		}
		else if(cache[lineC][i].lru == width-1)//Either we open spot or replace lru spot. This tracks lru
		{
			lruLoc = i;
		}
	}

	if(done == 0)//Did not find an open spot and had to replace the lru with the new block
	{
		if(cache[lineC][lruLoc].dirty == 1)//dirtybit requires a writeback
		{
			writeBack(cache, state , lruLoc, lineC, lineOffset, blockOffset, width);//write back call
		}
		print_action(startOfCacheBlk(cache, state , lruLoc, lineC,  lineOffset, blockOffset), blockSize, cache_to_nowhere);
		cache[lineC][lruLoc].valid = 1;//Set to new values
		cache[lineC][lruLoc].line = lineC;
		cache[lineC][lruLoc].tag = tagC;
		cache[lineC][lruLoc].dirty = 0;
		bound = cache[lineC][lruLoc].lru;
		updateLRU(cache, lineC, bound, width);//Update lrus
		cache[lineC][lruLoc].lru = 0;
		startOfBlk = loc - blockC;
		for(int j = 0; j < blockSize; j++)//set new block data values
		{
			cache[lineC][lruLoc].blockData[j] = state->mem[startOfBlk + j];		
		}
		result = lruLoc;		
	}
	return result;
}

int logTwo(int number)//This function serves as a log base 2 must be power of 2
{
	int shifts = 0;
	while(number != 1)
	{
		number = number>>1;
		shifts = shifts +1;
	}
	return shifts;
}

int blockStartOff(int loc, int blockSize)//Grabs start of cache block
{
	int result = loc - (loc%blockSize);//Uses the memory position to determine start
	return result;
	
}

void run(stateType* state, int blockSize, int nSets, int associativity){
	// Reused variables;
	int instr = 0;
	int regA = 0;
	int regB = 0;
	int offset = 0;
	int branchTarget = 0;
	int aluResult = 0;
	int total_instrs = 0;
	int blockOffset = logTwo(blockSize);// this is the same as log base 2 of blocksize
	int lineOffset = logTwo(nSets);// this is the same as log base 2 of nSets aka the number of lines
	int blk = 0;
	int line = 0;
	int tag = 0;
	block** cache = (block**)malloc(nSets*sizeof(block*));//Intializes the cache according to the dimensions
	for(int i = 0; i < nSets; i++)
	{
		cache[i] = (block*)malloc(associativity * sizeof(block));
		for(int j = 0; j < associativity; j++)//initializes each block of the cache to default setting
		{
			cache[i][j].valid = 0;//set all to invalid or empty sets
			cache[i][j].dirty = 0;
			cache[i][j].line = 0;
			cache[i][j].tag = 0;
			cache[i][j].lru = associativity-1;
			cache[i][j].blockData = malloc(blockSize*sizeof(int));//set to the size of the block we grab from memory
		}
	}

	// Primary loop
	while(1){
		total_instrs++;

		int hit = hitCheck(cache, state->pc, lineOffset, blockOffset, associativity);
		blk = blockField(state->pc, blockOffset);
		line = lineField(state->pc, lineOffset, blockOffset);
		tag = tagField(state->pc, lineOffset, blockOffset);

		// Instruction Fetch
		if(hit != -1)//hit
		{
			state->hits =  state->hits+1;
			instr = cache[line][hit].blockData[blk];//Grab instruction from cache
			updateLRU(cache, line, cache[line][hit].lru, associativity);//update LRUs 
			cache[line][hit].lru = 0;
			print_action(state->pc, 1, cache_to_processor);
		}
		else
		{
			state->misses =  state->misses+1;
			hit = findValidSpot(state, cache, state->pc, lineOffset, blockOffset, blockSize, associativity);//move instrution into cache
			print_action(blockStartOff(state->pc, blockSize), blockSize, memory_to_cache);
			instr = cache[line][hit].blockData[blk];//Grab instruction from cache
			cache[line][hit].lru = 0;
			print_action(state->pc, 1, cache_to_processor);
		}
		

		/* check for halt */
		if (opcode(instr) == HALT) {
			for(int i = 0; i < nSets; i++)//loop through all cache blocks in search of dirty bits
			{
				for(int j = 0; j < associativity; j++)
				{
					if(cache[i][j].dirty == 1)//If dirty then writeback
					{
						writeBack(cache, state, j, i, lineOffset, blockOffset, associativity);
					}
				}
			}
			break;
		}

		// Increment the PC
		state->pc = state->pc+1;

		// Set reg A and B
		regA = state->reg[field0(instr)];
		regB = state->reg[field1(instr)];

		// Set sign extended offset
		offset = signExtend(field2(instr));

		// Branch target gets set regardless of instruction
		branchTarget = state->pc + offset;

		/**
		 *
		 * Action depends on instruction
		 *
		 **/
		// ADD
		if(opcode(instr) == ADD){
			// Add
			aluResult = regA + regB;
			// Save result
			state->reg[field2(instr)] = aluResult;
		}
		// NAND
		else if(opcode(instr) == NAND){
			// NAND
			aluResult = ~(regA & regB);
			// Save result
			state->reg[field2(instr)] = aluResult;
		}
					

		// LW or SW
		else if(opcode(instr) == LW || opcode(instr) == SW){
			// Calculate memory address
			aluResult = regB + offset;
			int hit = hitCheck(cache,aluResult , lineOffset, blockOffset, associativity);//Checks to see if memory
			
			//Grabs fields of LW or SW memory position
			blk = blockField(aluResult , blockOffset);
			line = lineField(aluResult , lineOffset, blockOffset);
			tag = tagField(aluResult, lineOffset, blockOffset);


			if(opcode(instr) == LW){
				// Load
				if(hit != -1)//Hit for lw 
				{
					state->hits =  state->hits+1;
					state->reg[field0(instr)] = cache[line][hit].blockData[blk];//Hit grab from memory
					updateLRU(cache, line, cache[line][hit].lru, associativity);
					cache[line][hit].lru = 0;
					print_action(aluResult , 1, cache_to_processor)	;			
				}


				else//load up value into cache and load it into regisiter from cache
				{
					state->misses =  state->misses+1;
					hit = findValidSpot(state, cache, aluResult , lineOffset, blockOffset, blockSize, associativity);//Find a valid spot for the block
					print_action(blockStartOff(aluResult , blockSize), blockSize, memory_to_cache);
					state->reg[field0(instr)] = cache[line][hit].blockData[blk];
					cache[line][hit].lru = 0;
					print_action(aluResult , 1, cache_to_processor);
				}

			}else if(opcode(instr) == SW){
				// Store
				if(hit != -1)//hit for lw 
				{
					state->hits =  state->hits+1;
					cache[line][hit].blockData[blk] = regA;
					updateLRU(cache, line, cache[line][hit].lru, associativity);
					cache[line][hit].lru = 0;
					print_action(aluResult , blockSize, processor_to_cache);
				}
				else//load up value into cache and load it into regisiter from cache
				{
					state->misses =  state->misses+1;
					hit = findValidSpot(state, cache, aluResult , lineOffset, blockOffset, blockSize, associativity);//Enter into cache store word memory block
					print_action(blockStartOff(aluResult , blockSize), blockSize, memory_to_cache);
					cache[line][hit].blockData[blk] = regA;//change memory to new memory
					print_action(aluResult , 1, processor_to_cache);
					cache[line][hit].lru = 0;
				}
				cache[line][hit].dirty = 1;//memory block is now dirty
			}
		}
		// JALR
		else if(opcode(instr) == JALR){
			// rA != rB for JALR to work
			// Save pc+1 in regA
			state->reg[field0(instr)] = state->pc;
			//Jump to the address in regB;
			state->pc = state->reg[field1(instr)];
		}
		// BEQ
		else if(opcode(instr) == BEQ){
			// Calculate condition
			aluResult = (regA - regB);

			// ZD
			if(aluResult==0){
				// branch
				state->pc = branchTarget;
			}
		}	
	} // While
	print_stats(state);
	
}

int main(int argc, char** argv){

	/** Get command line arguments **/
	char* fname;

	opterr = 0;
	char* input; 
	int cin = 0;
	int blockSize = 0;
	int nSets = 0;
	int associativity = 0;

	while((cin = getopt(argc, argv, "f:b:s:a:")) != -1){
		switch(cin)
		{
			case 'f':
				fname=(char*)malloc(strlen(optarg));
				fname[0] = '\0';
				strncpy(fname, optarg, strlen(optarg)+1);
				printf("FILE: %s\n", fname);
				break;
			case 'b'://blocksize
				input = (char*)malloc(strlen(optarg));
				input[0] = '\0';
				strncpy(input, optarg, strlen(optarg)+1);
				blockSize = atoi(input);
				break;
			case 's'://number of sets
				input = (char*)malloc(strlen(optarg));
				input[0] = '\0';
				strncpy(input, optarg, strlen(optarg)+1);
				nSets = atoi(input);

				break;
			case 'a'://associativity 
				input = (char*)malloc(strlen(optarg));
				input[0] = '\0';
				strncpy(input, optarg, strlen(optarg)+1);
				associativity = atoi(input);
				break;

			case '?':
				if(optopt == 'f'){
					printf("Option -%c requires an argument.\n", optopt);
				}
				else if(isprint(optopt)){
					printf("Unknown option `-%c'.\n", optopt);
				}
				else{
					printf("Unknown option character `\\x%x'.\n", optopt);
					return 1;
				}
				break;
			default:
				abort();
		}
	}

	FILE *fp = fopen(fname, "r");
	if (fp == NULL) {
		printf("Cannot open file '%s' : %s\n", fname, strerror(errno));
		return -1;
	}

	/* count the number of lines by counting newline characters */
	int line_count = 0;
	int c;
	while (EOF != (c=getc(fp))) {
		if ( c == '\n' ){
			line_count++;
		}
	}
	// reset fp to the beginning of the file
	rewind(fp);

	stateType* state = (stateType*)malloc(sizeof(stateType));

	state->pc = 0;
	memset(state->mem, 0, NUMMEMORY*sizeof(int));
	memset(state->reg, 0, NUMREGS*sizeof(int));

	state->numMemory = line_count;

	char line[256];

	int i = 0;
	while (fgets(line, sizeof(line), fp)) {
		/* note that fgets doesn't strip the terminating \n, checking its
		   presence would allow to handle lines longer that sizeof(line) */
		state->mem[i] = atoi(line);
		i++;
	}
	fclose(fp);
	/** Run the simulation **/
	run(state, blockSize, nSets, associativity);

	free(state);
	free(fname);

}

