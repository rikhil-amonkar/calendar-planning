from z3 import *

def main():
    # Fixed day for the meeting
    day = "Monday"
    duration = 30  # minutes

    # Work hours in minutes (from 9:00 as 0 minutes to 17:00 as 480 minutes)
    work_start = 0
    work_end = 480

    # Define the start time variable in minutes from 9:00
    s = Int('s')

    solver = Solver()

    # Constraint: meeting must be within work hours
    solver.add(s >= work_start)
    solver.add(s + duration <= work_end)

    # Nicole's busy intervals in minutes (relative to 9:00)
    intervals = [(0, 60), (90, 450)]
    for (a, b) in intervals:
        # Meeting must not overlap: it must end before the interval starts or start after the interval ends
        solver.add(Or(s + duration <= a, s >= b))

    # Preference: Nicole prefers not to meet before 16:00 (420 minutes from 9:00)
    solver.push()
    solver.add(s >= 420)  # Try to satisfy preference

    if solver.check() == sat:
        model = solver.model()
        start_minutes_rel = model[s].as_long()
        solver.pop()
    else:
        solver.pop()  # Remove the preference constraint
        if solver.check() == sat:
            model = solver.model()
            start_minutes_rel = model[s].as_long()
        else:
            # Fallback: no solution found (should not happen per problem statement)
            print("No solution found")
            return

    # Convert start time from minutes to HH:MM format
    total_minutes_start = start_minutes_rel
    hours_start = 9 + total_minutes_start // 60
    minutes_start = total_minutes_start % 60
    start_time = f"{hours_start}:{minutes_start:02d}"

    # Calculate end time
    total_minutes_end = start_minutes_rel + duration
    hours_end = 9 + total_minutes_end // 60
    minutes_end = total_minutes_end % 60
    end_time = f"{hours_end}:{minutes_end:02d}"

    # Output the meeting details
    print(f"{day}, {start_time} to {end_time}")

if __name__ == "__main__":
    main()