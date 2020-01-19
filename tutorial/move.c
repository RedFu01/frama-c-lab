
/*@ requires v_x == 0.3 && v_y == 0.1;
  @ ensures \old(needle_x) == needle_x + v_x;
  @ ensures \old(needle_y) == needle_y + v_y;	
  @ assigns needle_x, needle_y;
  @*/
void main()
{
    // double needle_x = 0.0;
    // double needle_y = 0.0;

    // double v_x = 0.3;
    // double v_y = 0.1;
}


/*@ requires \valid(needle_x) && \valid(needle_y);
  @ ensures \old(*needle_x) == *needle_x + v_x;
  @ ensures \old(*needle_y) == *needle_y + v_y;	
  @ assigns *needle_x, *needle_y;
  @*/
void move(double *needle_x, double *needle_y, double v_x, double v_y) {
    *needle_x += v_x;
    *needle_y += v_y;
    return;
}