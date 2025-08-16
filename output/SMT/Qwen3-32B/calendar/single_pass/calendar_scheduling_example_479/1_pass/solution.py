from z3 import *

def main():
    solver = Solver()
    start = Int('start')
    solver.add(start >= 540)  # 9:00 AM in minutes
    solver.add(start <= 960)  # 4:00 PM in minutes (latest start for 1-hour meeting)

    # Collect all busy intervals from all participants
    busy_intervals = [
        # Joshua's busy intervals
        (660, 750),  # 11:00-12:30
        (810, 870),  # 13:30-14:30
        (990, 1020), # 16:30-17:00
        # Jerry's busy intervals
        (540, 570),  # 9:00-9:30
        (630, 720),  # 10:30-12:00
        (750, 780),  # 12:30-13:00
        (810, 840),  # 13:30-14:00
        (870, 900),  # 14:30-15:00
        (930, 960),  # 15:30-16:00
        # Jesse's busy intervals
        (540, 570),  # 9:00-9:30
        (630, 720),  # 10:30-12:00
        (750, 780),  # 12:30-13:00
        (870, 900),  # 14:30-15:00
        (930, 990),  # 15:30-16:30
        # Kenneth's busy intervals
        (630, 750),  # 10:30-12:30
        (810, 840),  # 13:30-14:00
        (870, 900),  # 14:30-15:00
        (930, 960),  # 15:30-16:00
        (990, 1020), # 16:30-17:00
    ]

    # Add constraints for each busy interval
    for b_start, b_end in busy_intervals:
        solver.add(Or(start + 60 <= b_start, start >= b_end))

    if solver.check() == sat:
        model = solver.model()
        start_val = model[start].as_long()
        day = "Monday"
        start_hours = start_val // 60
        start_minutes = start_val % 60
        start_time_str = f"{start_hours:02d}:{start_minutes:02d}"
        end_val = start_val + 60
        end_hours = end_val // 60
        end_minutes = end_val % 60
        end_time_str = f"{end_hours:02d}:{end_minutes:02d}"
        print("SOLUTION:")
        print(f"Day: {day}")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()