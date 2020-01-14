#include <stdio.h>
#include <stdbool.h>

double target_x = 100.0;
double target_y = 2.0;
double target_radius = 5.0;
double needle_x = 0.0;
double needle_y = 0.0;

double v_x = 0.3;
double v_y = 0.1;

// Declare functions
bool is_in_target_region();
bool is_in_safe_corridor();
bool is_out_of_bounds();
void rotate();
void move();
void reset();
double pow2(double a);

/*@ ensures (needle_x - target_x) * (needle_x - target_x) + (needle_y - target_y) + (needle_y - target_y) <= target_radius * target_radius;
  @ assigns needle_x, needle_y, v_y;
  @*/
int main(int argc, char *argv[])
{
	/*@ loop invariant (needle_x - target_x) * (needle_x - target_x) + (needle_y - target_y) + (needle_y - target_y) > target_radius * target_radius;
 	  @*/
	while (!is_in_target_region())
	{
		move();
		if (!is_in_safe_corridor())
		{
			rotate();
		}

		if(is_out_of_bounds()) {
			printf("Can't reach target. Resetting...");
			reset();
		}
	}

	printf("Succeeded!\n");
	printf("x=%f, y=%f", needle_x, needle_y);

	return 0;
}

/*@ assigns \nothing;
  @ behavior positive:
  @	  assumes (needle_x - target_x) * (needle_x - target_x) + (needle_y - target_y) * (needle_y - target_y) <= target_radius * target_radius;
  @	  ensures \result == true;
  @
  @ behavior negative:
  @	  assumes (needle_x - target_x) * (needle_x - target_x) + (needle_y - target_y) * (needle_y - target_y) > target_radius * target_radius;
  @	  ensures \result == false;
  @*/
bool is_in_target_region()
{
	return pow2(needle_x - target_x) + pow2(needle_y - target_y) <= pow2(target_radius);
}

/*@ assigns \nothing;
  @ behavior positive:
  @	  assumes (needle_y - target_y) * (needle_y - target_y) <= target_radius;
  @	  ensures \result == true;
  @
  @ behavior negative:
  @	  assumes (needle_y - target_y) * (needle_y - target_y) > target_radius;
  @	  ensures \result == false;
  @*/
bool is_in_safe_corridor()
{
	return pow2(needle_y - target_y) <= pow2(target_radius);
}

/*@ assigns \nothing;
  @ ensures \result == false; 
*/
bool is_out_of_bounds() {
	return false;
}

/*@ ensures \old(v_y) == -1* v_y;
  @ assigns v_y;
  @*/
void rotate()
{
	v_y *= -1;
}

/*@ ensures \old(needle_x) == needle_x + v_x;
  @ ensures \old(needle_y) == needle_y + v_y;	
  @ assigns needle_x, needle_y;
  @*/
void move()
{
	needle_x += v_x;
	needle_y += v_y;
}

/*@ assigns needle_x, needle_y;
  @ ensures needle_x == 0; 
  @ ensures needle_y == 0; 
*/
void reset()
{
	needle_x = 0.0;
	needle_y = 0.0;
}


/*@ ensures \result == a*a;
  @ assigns \nothing;
*/
double pow2(double a) {
	return a*a;
}