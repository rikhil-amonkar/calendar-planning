from z3 import *

def solve_scheduling():
    # Create solver instance
    s = Solver()

    # Define variables
    day = Int('day')  # 0: Monday, 1: Tuesday, 2: Wednesday, 3: Thursday, 4: Friday
    start_time = Int('start_time')  # in minutes from 9:00 (e.g., 0 means 9:00, 60 means 10:00, etc.)

    # Constants
    meeting_duration = 60  # minutes
    work_start = 0  # 9:00 is 0 minutes from 9:00
    work_end = 8 * 60  # 17:00 is 8*60=480 minutes from 9:00 (540 to 1020 in day minutes)

    # Constraints for day and start time
    s.add(day >= 0, day <= 4)  # Monday to Friday
    s.add(start_time >= work_start)
    s.add(start_time + meeting_duration <= work_end)

    # Define busy slots for Diane and Matthew
    # Each slot is (day, start_min, end_min) where start_min and end_min are from 9:00 as 0
    diane_busy = [
        (0, 3*60, 3*60 + 30),  # Monday 12:00-12:30 (3h from 9:00)
        (0, 6*60, 6*60 + 30),   # Monday 15:00-15:30
        (1, 1*60, 2*60),        # Tuesday 10:00-11:00
        (1, 2*60 + 30, 3*60),   # Tuesday 11:30-12:00
        (1, 3*60 + 30, 4*60),   # Tuesday 12:30-13:00
        (1, 7*60, 8*60),        # Tuesday 16:00-17:00
        (2, 0, 30),             # Wednesday 9:00-9:30
        (2, 5*60 + 30, 6*60),   # Wednesday 14:30-15:00
        (2, 7*60 + 30, 8*60),   # Wednesday 16:30-17:00
        (3, 6*60 + 30, 7*60 + 30),  # Thursday 15:30-16:30
        (4, 30, 2*60 + 30),     # Friday 9:30-11:30
        (4, 5*60 + 30, 6*60),   # Friday 14:30-15:00
        (4, 7*60, 8*60)         # Friday 16:00-17:00
    ]

    matthew_busy = [
        (0, 0, 1*60),           # Monday 9:00-10:00
        (0, 1*60 + 30, 8*60),   # Monday 10:30-17:00
        (1, 0, 8*60),           # Tuesday 9:00-17:00
        (2, 0, 2*60),           # Wednesday 9:00-11:00
        (2, 3*60, 5*60 + 30),   # Wednesday 12:00-14:30
        (2, 7*60, 8*60),        # Wednesday 16:00-17:00
        (3, 0, 7*60),           # Thursday 9:00-16:00
        (4, 0, 8*60)            # Friday 9:00-17:00
    ]

    # Function to add no-overlap constraints
    def add_no_overlap_constraints(busy_slots):
        for (d, busy_start, busy_end) in busy_slots:
            s.add(Not(And(
                day == d,
                start_time < busy_end,
                start_time + meeting_duration > busy_start
            )))

    # Add constraints for Diane and Matthew
    add_no_overlap_constraints(diane_busy)
    add_no_overlap_constraints(matthew_busy)

    # Matthew's preference: not Wednesday before 12:30 (which is 3h30 from 9:00 = 210 minutes)
    s.add(Not(And(day == 2, start_time < 3*60 + 30)))  # 3*60 +30 = 210 minutes (12:30 is 3h30 from 9:00)

    # Check for solution
    if s.check() == sat:
        m = s.model()
        day_val = m[day].as_long()
        start_val = m[start_time].as_long()

        # Convert day_val to day name
        days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
        day_name = days[day_val]

        # Calculate start and end times in HH:MM format
        total_minutes_start = 540 + start_val  # 9:00 is 540 minutes
        hours_start = total_minutes_start // 60
        minutes_start = total_minutes_start % 60
        start_time_str = f"{hours_start:02d}:{minutes_start:02d}"

        total_minutes_end = total_minutes_start + meeting_duration
        hours_end = total_minutes_end // 60
        minutes_end = total_minutes_end % 60
        end_time_str = f"{hours_end:02d}:{minutes_end:02d}"

        # Print solution
        print("SOLUTION:")
        print(f"Day: {day_name}")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

solve_scheduling()