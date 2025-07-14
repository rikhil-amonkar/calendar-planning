from z3 import *

def solve_scheduling():
    # Create a solver instance
    s = Solver()

    # Possible days: Monday (0) or Tuesday (1)
    day = Int('day')
    s.add(Or(day == 0, day == 1))

    # Meeting start time in minutes from 9:00 (540 minutes)
    start_time = Int('start_time')
    # Meeting duration is 30 minutes
    meeting_duration = 30
    end_time = start_time + meeting_duration

    # Working hours: 9:00 to 17:00 (540 to 1020 minutes)
    s.add(start_time >= 540)  # 9:00 in minutes
    s.add(end_time <= 1020)   # 17:00 in minutes

    # Amanda's busy slots in minutes from start of day (9:00 is 0)
    amanda_busy = {
        0: [(540, 630), (660, 690), (750, 780), (810, 840), (870, 900)],  # Monday
        1: [(540, 570), (600, 630), (690, 720), (810, 900), (930, 960), (990, 1020)]  # Tuesday
    }

    # Nathan's busy slots in minutes from start of day (9:00 is 0)
    nathan_busy = {
        0: [(600, 630), (660, 690), (810, 900), (960, 990)],  # Monday
        1: [(540, 630), (660, 780), (810, 840), (870, 930), (960, 990)]  # Tuesday
    }

    # Amanda does not want to meet on Tuesday after 11:00 (660 minutes from 9:00)
    s.add(Implies(day == 1, start_time < 660))

    # Nathan cannot meet on Monday
    s.add(day != 0)

    # Function to check if the meeting overlaps with any busy interval
    def no_overlap(day_val, start, end, busy_intervals):
        constraints = []
        for (busy_start, busy_end) in busy_intervals.get(day_val, []):
            constraints.append(Or(end <= busy_start, start >= busy_end))
        return And(*constraints) if constraints else True

    # Add constraints for Amanda's busy times
    amanda_no_overlap = no_overlap(day, start_time, end_time, amanda_busy)
    s.add(amanda_no_overlap)

    # Add constraints for Nathan's busy times
    nathan_no_overlap = no_overlap(day, start_time, end_time, nathan_busy)
    s.add(nathan_no_overlap)

    # Check for a solution
    if s.check() == sat:
        model = s.model()
        day_val = model[day].as_long()
        start_min = model[start_time].as_long()

        # Determine day name
        day_name = "Monday" if day_val == 0 else "Tuesday"

        # Convert start and end times to HH:MM format
        start_hh = start_min // 60
        start_mm = start_min % 60
        end_min = start_min + meeting_duration
        end_hh = end_min // 60
        end_mm = end_min % 60

        # Format the times as strings with leading zeros
        start_time_str = f"{start_hh:02d}:{start_mm:02d}"
        end_time_str = f"{end_hh:02d}:{end_mm:02d}"

        print("SOLUTION:")
        print(f"Day: {day_name}")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

solve_scheduling()