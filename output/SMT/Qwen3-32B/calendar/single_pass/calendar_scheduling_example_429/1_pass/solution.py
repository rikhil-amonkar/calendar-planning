from z3 import *

def main():
    solver = Solver()

    start = Int('start')

    # Define the overall time constraints (9:00 AM to 4:30 PM for a 30-minute meeting ending by 5:00 PM)
    solver.add(start >= 540)  # 9:00 AM in minutes
    solver.add(start <= 990)  # 4:30 PM in minutes (990 + 30 = 1020, which is 5:00 PM)

    # Collect all busy intervals (in minutes since midnight)
    busy_intervals = [
        # Judy
        (780, 810), (960, 990),
        # Olivia
        (600, 630), (720, 780), (840, 870),
        # Jacqueline
        (600, 630), (900, 930),
        # Laura
        (540, 600), (630, 720), (780, 810), (870, 900), (930, 1020),
        # Tyler
        (540, 600), (660, 690), (750, 780), (840, 870), (930, 1020),
        # Lisa
        (570, 630), (660, 690), (720, 750), (780, 810), (840, 870), (960, 1020)
    ]

    # Add constraints for each busy interval
    for busy_start, busy_end in busy_intervals:
        solver.add(Or(start >= busy_end, start + 30 <= busy_start))

    # Check for solution
    if solver.check() == sat:
        model = solver.model()
        start_val = model[start].as_long()
        end_val = start_val + 30
        # Format the start and end times
        def format_time(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{hours:02d}:{mins:02d}"
        day = "Monday"
        start_time = format_time(start_val)
        end_time = format_time(end_val)
        print("SOLUTION:")
        print(f"Day: {day}")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()