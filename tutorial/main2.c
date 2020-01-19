#include <stdio.h>
#include <stdbool.h>

double target_x = 1000.0;
double target_y = 20.0;
double target_radius = 5.0;
double needle_x = 0.0;
double needle_y = 0.0;

double v_x = 0.3;
double v_y = 0.1;


double distance_thresholds[2] = {50, 0};
double velocities_x[2] = {0.3, 0.1};
double velocities_y[2] = {0.1, 0.01};

// Declare functions
void update_velocities();
bool is_in_target_region();
bool is_in_safe_corridor();
bool is_out_of_bounds();
void rotate();
void move();
void reset();
double pow2(double a);


/*@ ensures (needle_x - target_x) * (needle_x - target_x) + (needle_y - target_y) * (needle_y - target_y) <= target_radius * target_radius;
  @ ensures \result == true;
  @ assigns needle_x, needle_y, v_y;
  @*/
bool main(int argc, char *argv[])
{
	/*@ loop invariant needle_x >= 0 && needle_x <= target_x + target_radius;
 	  @ loop assigns v_y;
    @*/
	while (!is_in_target_region())
	{
		if (!is_in_safe_corridor())
		{
			rotate();
		}
    update_velocities();
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

/*@ requires target_y >= 0;
  @ assigns \nothing;
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

/*@ ensures v_x == velocities_x[0] || v_x == velocities_x[1];
  @ ensures v_y == velocities_y[0] || v_y == velocities_y[1];
  @ assigns v_x, v_y;
  @*/
void update_velocities() {

    v_x = velocities_x[0];
    v_y = velocities_y[0];

    return;
    // double distance = target_x - needle_x;
    // /*@ loop invariant v_x == velocities_x[0] || v_x == velocities_x[1];
    //   @ loop invariant v_y == velocities_y[0] || v_y == velocities_y[1];
 	//   @ loop assigns i, v_x, v_y;
    //   @ loop variant 2-i;
    // @*/
    // for(int i = 0; i< 2; i++) {
    //     if(distance > distance_thresholds[i]) {
    //         v_x = velocities_x[i];
    //         v_y = velocities_y[i];
    //     }
    // }
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