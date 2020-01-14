#include <stdio.h>
#include <stdbool.h>

int target_x = 1;
int target_y = 10;
int needle_x = 0;
int needle_y = 0;

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

	printf("Succeeded");
	printf("x=%d, y=%d", target_x, target_y);

	return 0;
}

bool is_in_target_region()
{
	return false;
}

bool is_in_safe_corridor()
{
	return false;
}

bool is_out_of_bounds() {
	return false;
}

void rotate()
{
}

void move()
{
}

void reset()
{
}