/*
TERMINATION

suggested parameters:
- partition abstract domain = boxes [default]
- function abstract domain = affine [default]
- backward widening delay = 2 [default]
*/

int main(int input1, int input2) {
  int x = 1, y = 1, z=1; 
  if (input1>0) { 
  	x = x + 5; 
  	y = y + 6; 
  	z = z + 4; }
  if (input2>0) { 
  	x = x + 6; 
  	y = y + 5; 
  	z = z + 4; }  	 
  assert((x>6) || (y>7));

}
