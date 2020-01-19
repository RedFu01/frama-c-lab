#include <stdio.h>
#include <stdbool.h>

double target_points_x[2] = {100.0, 120.0};
double target_points_y[2] = {2.0, 4.0};

bool successes[2] = {false, false};

double target_x = 0.0;
double target_y = 0.0;
double target_radius = 20.0;
double needle_x = 0.0;
double needle_y = 0.0;

double v_x = 0.3;
double v_y = 0.1;

// Declare functions
bool check_one();
bool is_in_target_region();
bool is_in_safe_corridor();
bool is_out_of_bounds();
void rotate();
void move();
void reset();
double pow2(double a);

/*@ ensures \forall integer j; 0 <= j < 2 ==> successes[j] == 1;
  @ assigns successes[0..1], target_x, target_y, needle_x, needle_y, v_y;
  @*/
int main(int argc, char *argv[]) {
	/*@ loop invariant \forall integer k; 0 <= k < i ==> successes[k] == true;
    @ loop invariant 0 <= i <= 2;
 	  @ loop assigns i, target_x, target_y, needle_x, needle_y, v_y, successes[0..1];
    @ loop variant 2-i;
    @*/
  for(int i = 0; i< 2; i++) {
    target_x = target_points_x[i];
    target_y = target_points_y[i];
    successes[i] = check_one();
    reset();
  }

    // target_x = target_points_x[0];
    // target_y = target_points_y[0];
    // successes[0] = check_one();
    // reset();

    // target_x = target_points_x[1];
    // target_y = target_points_y[1];
    // successes[1] = check_one();
    // reset();
  return 0;
}

/*@ ensures (needle_x - target_x) * (needle_x - target_x) + (needle_y - target_y) * (needle_y - target_y) <= target_radius * target_radius;
  @ ensures \result == true;
  @ assigns needle_x, needle_y, v_y;
  @*/
bool check_one()
{
	/*@ loop assigns needle_x, needle_y, v_y;
    @*/
	while (!is_in_target_region())
	{
		if (!is_in_safe_corridor())
		{
			rotate();
		}

    move();

		if(is_out_of_bounds()) {
			//printf("Can't reach target. Resetting...");
			reset();
		}
	}

	// printf("Succeeded!\n");
	// printf("x=%f, y=%f\n", needle_x, needle_y);

	return true;
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
  @	  assumes (needle_y - target_y) * (needle_y - target_y) <= target_radius * target_radius;
  @	  ensures \result == true;
  @
  @ behavior negative:
  @	  assumes (needle_y - target_y) * (needle_y - target_y) > target_radius * target_radius;
  @	  ensures \result == false;
  @*/
bool is_in_safe_corridor()
{
	return pow2(needle_y - target_y) <= pow2(target_radius);
}

/*@ assigns \nothing;
  @ behavior positive:
  @	  assumes needle_x > target_x;
  @	  ensures \result == true;
  @
  @ behavior negative:
  @	  assumes needle_x <= target_x;
  @	  ensures \result == false;
  @*/

bool is_out_of_bounds() {
	return needle_x > target_x;
}

/*@ ensures \old(v_y) == -1* v_y;
  @ assigns v_y;
  @*/
void rotate()
{
	v_y *= -1;
}

/*@ ensures \old(needle_x) == needle_x - v_x;
  @ ensures \old(needle_y) == needle_y - v_y;	
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