from z3 import *

def solve_meeting_schedule():
    # Initialize the solver
    s = Solver()

    # Define variables
    day = Int('day')  # 0: Monday, 1: Tuesday, 2: Wednesday
    start_time = Int('start_time')  # in minutes from 9:00 (e.g., 0 is 9:00, 30 is 9:30)
    end_time = Int('end_time')

    # Meeting duration is 30 minutes
    s.add(end_time == start_time + 30)

    # Work hours are 9:00 to 17:00 (480 minutes from 9:00)
    s.add(start_time >= 0)
    s.add(end_time <= 480)

    # Day must be 0, 1, or 2 (Monday, Tuesday, Wednesday)
    s.add(day >= 0)
    s.add(day <= 2)

    # Susan's blocked times
    # Convert each blocked time to (day, start_min, end_min) tuples
    susan_blocked = [
        (0, 12*60 + 30 - 9*60, 13*60 - 9*60),  # Monday 12:30-13:00 (210-240 mins)
        (0, 13*60 + 30 - 9*60, 14*60 - 9*60),  # Monday 13:30-14:00 (270-300 mins)
        (1, 11*60 + 30 - 9*60, 12*60 - 9*60),  # Tuesday 11:30-12:00 (150-180 mins)
        (2, 9*60 + 30 - 9*60, 10*60 + 30 - 9*60),  # Wednesday 9:30-10:30 (30-90 mins)
        (2, 14*60 - 9*60, 14*60 + 30 - 9*60),  # Wednesday 14:00-14:30 (300-330 mins)
        (2, 15*60 + 30 - 9*60, 16*60 + 30 - 9*60)  # Wednesday 15:30-16:30 (390-450 mins)
    ]

    # Sandra's blocked times
    sandra_blocked = [
        (0, 0, 13*60 - 9*60),  # Monday 9:00-13:00 (0-240 mins)
        (0, 14*60 - 9*60, 15*60 - 9*60),  # Monday 14:00-15:00 (300-360 mins)
        (0, 16*60 - 9*60, 16*60 + 30 - 9*60),  # Monday 16:00-16:30 (420-450 mins)
        (1, 0, 9*60 + 30 - 9*60),  # Tuesday 9:00-9:30 (0-30 mins)
        (1, 10*60 + 30 - 9*60, 12*60 - 9*60),  # Tuesday 10:30-12:00 (90-180 mins)
        (1, 12*60 + 30 - 9*60, 13*60 + 30 - 9*60),  # Tuesday 12:30-13:30 (210-270 mins)
        (1, 14*60 - 9*60, 14*60 + 30 - 9*60),  # Tuesday 14:00-14:30 (300-330 mins)
        (1, 16*60 - 9*60, 17*60 - 9*60),  # Tuesday 16:00-17:00 (420-480 mins)
        (2, 0, 11*60 + 30 - 9*60),  # Wednesday 9:00-11:30 (0-150 mins)
        (2, 12*60 - 9*60, 12*60 + 30 - 9*60),  # Wednesday 12:00-12:30 (180-210 mins)
        (2, 13*60 - 9*60, 17*60 - 9*60)  # Wednesday 13:00-17:00 (240-480 mins)
    ]

    # Function to add no overlap constraints for a list of blocked times
    def add_no_overlap_constraints(blocked_times):
        for (b_day, b_start, b_end) in blocked_times:
            s.add(Not(And(
                day == b_day,
                start_time < b_end,
                end_time > b_start
            )))

    # Add constraints for Susan and Sandra's blocked times
    add_no_overlap_constraints(susan_blocked)
    add_no_overlap_constraints(sandra_blocked)

    # Susan would rather not meet on Tuesday (day 1)
    s.add(day != 1)

    # Sandra cannot meet on Monday after 16:00 (420 minutes from 9:00 is 16:00)
    # So on Monday (day 0), the meeting must end by 16:00 (420 minutes)
    s.add(Implies(day == 0, end_time <= 420))

    # Check for a solution
    if s.check() == sat:
        model = s.model()
        day_val = model[day].as_long()
        start_val = model[start_time].as_long()
        end_val = model[end_time].as_long()

        # Convert day_val to day name
        days = ['Monday', 'Tuesday', 'Wednesday']
        day_name = days[day_val]

        # Convert start and end times to HH:MM format
        start_hour = 9 + start_val // 60
        start_min = start_val % 60
        end_hour = 9 + end_val // 60
        end_min = end_val % 60

        # Format as strings
        start_time_str = f"{start_hour:02d}:{start_min:02d}"
        end_time_str = f"{end_hour:02d}:{end_min:02d}"

        # Print the solution
        print("SOLUTION:")
        print(f"Day: {day_name}")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

solve_meeting_schedule()