from z3 import *

def main():
    solver = Solver()
    start_time = Int('start_time')

    # Work hours constraints (9:00 to 17:00, 540 to 1020 minutes)
    solver.add(start_time >= 540)
    solver.add(start_time <= 960)  # end time is start_time + 60 <= 1020

    # Define blocked intervals for each participant in minutes since midnight
    olivia_blocks = [(750, 810), (870, 900), (990, 1020)]
    virginia_blocks = [(540, 600), (690, 960), (990, 1020)]
    paul_blocks = [(540, 570), (660, 690), (780, 840), (870, 960), (990, 1020)]

    # Add constraints for Olivia
    for b_start, b_end in olivia_blocks:
        solver.add(Or(start_time + 60 <= b_start, start_time >= b_end))

    # Add constraints for Virginia
    for b_start, b_end in virginia_blocks:
        solver.add(Or(start_time + 60 <= b_start, start_time >= b_end))

    # Add constraints for Paul
    for b_start, b_end in paul_blocks:
        solver.add(Or(start_time + 60 <= b_start, start_time >= b_end))

    if solver.check() == sat:
        model = solver.model()
        start_time_val = model.eval(start_time).as_long()
        end_time_val = start_time_val + 60

        # Convert to hours and minutes
        start_h, start_m = divmod(start_time_val, 60)
        end_h, end_m = divmod(end_time_val, 60)

        time_str = f"{start_h}:{start_m:02d}:{end_h}:{end_m:02d}"
        day_str = "Monday"
        print(f"{{time: {time_str}, day: {day_str}}}")
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()