from z3 import *

def solve_scheduling():
    # Create solver instance
    s = Solver()

    # Define possible days (0=Monday, 1=Tuesday, ..., 4=Friday)
    day = Int('day')
    s.add(day >= 0, day <= 4)

    # Define start time in minutes from 9:00 (0 = 9:00, 480 = 17:00)
    start_time = Int('start_time')
    s.add(start_time >= 0, start_time <= 480 - 60)  # Meeting duration is 60 minutes

    # Convert start_time to HH:MM format for constraints
    def time_to_hhmm(minutes):
        hours = 9 + minutes // 60
        mins = minutes % 60
        return hours, mins

    # Diane's busy times per day in minutes from 9:00
    diane_busy = {
        0: [(180, 210), (360, 390)],  # Monday: 12:00-12:30, 15:00-15:30
        1: [(60, 120), (150, 180), (210, 240), (420, 480)],  # Tuesday: 10:00-11:00, 11:30-12:00, 12:30-13:00, 16:00-17:00
        2: [(0, 30), (330, 360), (390, 480)],  # Wednesday: 9:00-9:30, 14:30-15:00, 16:30-17:00
        3: [(390, 450)],  # Thursday: 15:30-16:30
        4: [(30, 150), (330, 360), (420, 480)]  # Friday: 9:30-11:30, 14:30-15:00, 16:00-17:00
    }

    # Matthew's busy times per day in minutes from 9:00
    matthew_busy = {
        0: [(0, 60), (90, 480)],  # Monday: 9:00-10:00, 10:30-17:00
        1: [(0, 480)],  # Tuesday: 9:00-17:00
        2: [(0, 120), (180, 330), (420, 480)],  # Wednesday: 9:00-11:00, 12:00-14:30, 16:00-17:00
        3: [(0, 420)],  # Thursday: 9:00-16:00
        4: [(0, 480)]  # Friday: 9:00-17:00
    }

    # Matthew's preference: not on Wednesday before 12:30 (210 minutes from 9:00)
    s.add(Not(And(day == 2, start_time < 210)))

    # Function to check if the meeting overlaps with any busy interval
    def no_overlap(day_val, start, duration, busy_intervals):
        return And([Or(
            day != day_val,
            start >= end,
            start + duration <= begin
        ) for (begin, end) in busy_intervals])

    # Add constraints for Diane and Matthew
    for d in range(5):
        s.add(Implies(day == d, no_overlap(d, start_time, 60, diane_busy[d])))
        s.add(Implies(day == d, no_overlap(d, start_time, 60, matthew_busy[d])))

    # Check for solution
    if s.check() == sat:
        m = s.model()
        day_val = m[day].as_long()
        start_val = m[start_time].as_long()

        # Map day_val to day name
        days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
        day_name = days[day_val]

        # Convert start_val to HH:MM
        start_hour = 9 + start_val // 60
        start_min = start_val % 60
        end_hour = start_hour + 1
        end_min = start_min

        # Format start and end times as HH:MM
        start_time_str = f"{start_hour:02d}:{start_min:02d}"
        end_time_str = f"{end_hour:02d}:{end_min:02d}"

        # Print solution
        print("SOLUTION:")
        print(f"Day: {day_name}")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

solve_scheduling()