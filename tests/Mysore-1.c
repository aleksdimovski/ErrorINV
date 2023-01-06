// simple loop

// backward = forward


int main(int x) {
  //int x=10;
  int c=0;
  while (x+c >= 0) {  
    x = x - c;
    c = c + 1; 
  }
  assert (c>0);

}
