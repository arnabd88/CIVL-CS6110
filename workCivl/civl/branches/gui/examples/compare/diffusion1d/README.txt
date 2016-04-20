Here is some notes for comparing two diffusion1d programs(one in parallel and one in sequential) from FEVS.

Bugs of original MPI-C program( diffusion1d_par.c ):

1. Never try to free "u", which stores the final result, when quit by calling quit().

2. Never try to close the file, which provides input data, when quit by calling quit().

3. Malloc space to pointer "buf" inside the function "init()" twice without free the space 
   given by first time malloc.

4. Missing "fclose()" in function "init()".

5. Missing MPI_Finalize() when root process quits.

6. When root process call "quit()" before broadcasting parameters to
    other process,  other process will keep waiting for broadcasting forever.

Defects of CIVL:

1. CIVL cannot automatically handle system file closing work when the program quit before 
   reaching the end.

2. When comparing 2 programs, CIVL cannot recognize the file both of 2 programs are reading
   is same. Thus, CIVL will verify one path that one program quit because of failing on 
   reading file but the other doesn't fail on it.

3. "sprintf()" still not supported

4. CIVL pragma cannot support "if" statement.
