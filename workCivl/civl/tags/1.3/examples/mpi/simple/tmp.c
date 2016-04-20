int MPI_Reduce(void* _sendbuf, void* _recvbuf, int _count, MPI_Datatype _datatype,
               MPI_Op _op, int _root, MPI_Comm _comm) {
  int _i;
  int _j;
  double _tempBuffer[_count];
  int _rank;
  int _nprocs;
  
#pragma TASS assert MPIX_State == MPIX_INITIALIZED, "Attempt to call MPI_Reduce when MPI is not initialized";
#pragma TASS assert _op == MPI_SUM;
#pragma TASS assert _datatype == MPI_DOUBLE;
  MPI_Comm_rank(MPI_COMM_WORLD, &_rank);
  MPI_Comm_size(MPI_COMM_WORLD, &_nprocs);
  if (_rank == _root) {
    for (_j=0; _j<_count; _j++) _tempBuffer[_j] = ((double*)_sendbuf)[_j];
    for (_i=0; _i<_nprocs; _i++) {
      if (_i != _root) {
	MPI_Recv(_recvbuf, _count, _datatype, _i, MPIX_REDUCE_TAG, 
		 _comm, MPI_STATUS_IGNORE);
	for(_j=0; _j<_count; _j++) _tempBuffer[_j] += ((double*)_recvbuf)[_j];
      }
    }
    for (_j=0; _j<_count; _j++) ((double*)_recvbuf)[_j]=_tempBuffer[_j];
  } else {
    MPI_Send(_sendbuf, _count, _datatype, _root, MPIX_REDUCE_TAG, _comm);
  }
  return 0;
}

/* For now: just doubles and sum */
int MPI_Allreduce(void* _sendbuf, void* _recvbuf, int _count, MPI_Datatype _datatype,
                  MPI_Op _op, MPI_Comm _comm) {
  int _i;
  int _j;
  double _tempBuffer[_count];
  
  #pragma TASS assert MPIX_State == MPIX_INITIALIZED, "Attempt to call MPI_Allreduce when MPI is not initialized";
  #pragma TASS assert _op == MPI_SUM;
  #pragma TASS assert _datatype == MPI_DOUBLE;
  if (PID == 0) {
    for (_j=0; _j<_count; _j++) _tempBuffer[_j] = ((double*)_sendbuf)[_j];
  	for (_i=1; _i<NPROCS; _i++) {
  	  MPI_Recv(_recvbuf, _count, _datatype, _i, MPIX_ALLREDUCE_TAG, 
  	           _comm, MPI_STATUS_IGNORE);
  	  for(_j=0; _j<_count; _j++) _tempBuffer[_j] += ((double*)_recvbuf)[_j];
  	}
  	for (_j=0; _j<_count; _j++) ((double*)_recvbuf)[_j]=_tempBuffer[_j];
  	for (_i=1; _i<NPROCS; _i++) {
  	  MPI_Send(_recvbuf, _count, _datatype, _i, MPIX_ALLREDUCE_TAG, _comm);
  	}
  } else {
    MPI_Send(_sendbuf, _count, _datatype, 0, MPIX_ALLREDUCE_TAG, _comm);
    MPI_Recv(_recvbuf, _count, _datatype, 0, MPIX_ALLREDUCE_TAG, _comm,
             MPI_STATUS_IGNORE);
  }
  return 0;
}
