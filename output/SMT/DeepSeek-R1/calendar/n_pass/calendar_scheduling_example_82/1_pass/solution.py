from z3 import *

def main():
    # Initialize variables
    s = Int('start')
    duration = 30
    total_minutes_in_work_day = 8 * 60  # 9:00 to 17:00 is 8 hours = 480 minutes

    # Constraints: meeting must start between 0 and (480 - duration) minutes
    constraints = [s >= 0, s <= total_minutes_in_work_day - duration]

    # Michael's busy intervals (in minutes from 9:00)
    michael_busy = [
        (30, 90),    # 9:30-10:30
        (360, 390),  # 15:00-15:30
        (420, 450)   # 16:00-16:30
    ]
    for start_busy, end_busy in michael_busy:
        constraints.append(Or(s + duration <= start_busy, s >= end_busy))

    # Eric has no busy intervals

    # Arthur's busy intervals (in minutes from 9:00)
    arthur_busy = [
        (0, 180),    # 9:00-12:00
        (240, 360),  # 13:00-15:00
        (390, 420),  # 15:30-16:00
        (450, 480)   # 16:30-17:00
    ]
    for start_busy, end_busy in arthur_busy:
        constraints.append(Or(s + duration <= start_busy, s >= end_busy))

    # Solve constraints
    solver = Solver()
    solver.add(constraints)
    if solver.check() == sat:
        model = solver.model()
        start_val = model[s].as_long()
        # Convert start time from minutes to HH:MM format
        start_hour = 9 + start_val // 60
        start_minute = start_val % 60
        start_time = f"{start_hour:02d}:{start_minute:02d}"
        # Calculate end time
        end_val = start_val + duration
        end_hour = 9 + end_val // 60
        end_minute = end_val % 60
        end_time = f"{end_hour:02d}:{end_minute:02d}"
        # Output the solution
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()