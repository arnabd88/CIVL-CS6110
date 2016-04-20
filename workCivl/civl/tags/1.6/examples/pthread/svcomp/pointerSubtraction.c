struct device{
};
struct A{
    int a;
    int b;
};
struct my_data{
  int lock;
  struct device dev;
  struct A shared;
};
int main()
{
  struct my_data object;
  struct device* my_dev = &(object.dev);
  struct my_data* data;
  struct my_data* $sef$0;
  
  typeof(((struct my_data*)0)->dev)* __mptr = my_dev;
  data = (struct my_data*)((char*)__mptr - (unsigned long)(&(((struct my_data*)0)->dev)));
  (data)->shared.a = 1;
  (data)->shared.b = (data)->shared.b + 1;
}
