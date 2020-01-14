#include <stdio.h>
#include <stdbool.h>
#include <math.h>

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

/*@ ensures needle_x - target_x <= target_radius;
  @ ensures needle_y - target_y <= target_radius;
  @ assigns needle_x, needle_y;
  @*/
int main(int argc, char *argv[])
{
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

bool is_in_target_region()
{
	return pow(needle_x - target_x, 2) + pow(needle_y - target_y, 2) <= target_radius;
}

bool is_in_safe_corridor()
{
	printf("%f, %f\n", pow(needle_y - target_y, 2), pow(target_radius,2));
	return pow(needle_y - target_y, 2) <= pow(target_radius,2);
}

bool is_out_of_bounds() {
	return false;
}

/*@ ensures \old(v_y) == -1* v_y;
  @ assigns v_y;
  @*/
void rotate()
{
	v_y *= -1;
	printf("ROTATE \n");
}

/*@ ensures \old(needle_x) == needle_x + v_x;
  @ ensures \old(needle_y) == needle_y + v_y;	
  @ assigns needle_x, needle_y;
  @*/
void move()
{
	needle_x += v_x;
	needle_y += v_y;
	printf("MOVE \n");
}

void reset()
{
		printf("RESET \n");
}