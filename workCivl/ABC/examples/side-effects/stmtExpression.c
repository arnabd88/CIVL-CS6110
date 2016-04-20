int foo(){
  return 1;
}

int main(){
  int a=({ int y = foo (); int z;
        if (y > 0) z = y;
        else z = - y;
        z; });
}
