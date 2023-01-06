// simple loop

// backward = forward


//int main(int x, int y) {
int main() {
  int x=7;
  int y=0;
  int z=y; 
  while (x > 0) {  
    if (x<3) y = y+1;
    else y = 1;
    x = x - 1; 
  }
  assert (y<=0);

}
