from z3 import *

def solve_meeting_scheduling():
    # Create the solver
    s = Solver()

    # Define the possible days
    days = ["Monday", "Tuesday"]
    day = Int('day')
    s.add(day >= 0, day < len(days))

    # Define the start and end times in minutes from 9:00 (540 minutes)
    start_time = Int('start_time')
    end_time = Int('end_time')
    meeting_duration = 30  # minutes

    # Work hours are 9:00 to 17:00 (540 to 1020 minutes)
    s.add(start_time >= 540, end_time <= 1020)
    s.add(end_time == start_time + meeting_duration)

    # Jean's busy times (in minutes from 9:00)
    jean_busy = [
        ("Tuesday", 11*60 + 30, 12*60 + 0),    # Tuesday 11:30-12:00
        ("Tuesday", 16*60 + 0, 16*60 + 30),     # Tuesday 16:00-16:30
    ]

    # Doris's busy times (in minutes from 9:00)
    doris_busy = [
        ("Monday", 9*60 + 0, 11*60 + 30),      # Monday 9:00-11:30
        ("Monday", 12*60 + 0, 12*60 + 30),      # Monday 12:00-12:30
        ("Monday", 13*60 + 30, 16*60 + 0),      # Monday 13:30-16:00
        ("Monday", 16*60 + 30, 17*60 + 0),      # Monday 16:30-17:00
        ("Tuesday", 9*60 + 0, 17*60 + 0),       # Tuesday 9:00-17:00
    ]

    # Doris prefers not to meet on Monday after 14:00 (840 minutes)
    # So we add a constraint that if the day is Monday, the meeting must end by 14:00
    s.add(Implies(day == 0, end_time <= 840))

    # Add constraints for Jean's busy times
    for busy_day, busy_start, busy_end in jean_busy:
        day_index = days.index(busy_day)
        s.add(Not(And(day == day_index,
                      start_time < busy_end,
                      end_time > busy_start)))

    # Add constraints for Doris's busy times
    for busy_day, busy_start, busy_end in doris_busy:
        day_index = days.index(busy_day)
        s.add(Not(And(day == day_index,
                      start_time < busy_end,
                      end_time > busy_start)))

    # Check for a solution
    if s.check() == sat:
        m = s.model()
        selected_day = days[m[day].as_long()]
        start_minutes = m[start_time].as_long()
        end_minutes = m[end_time].as_long()

        # Convert minutes back to HH:MM format
        start_hh = start_minutes // 60
        start_mm = start_minutes % 60
        end_hh = end_minutes // 60
        end_mm = end_minutes % 60

        print("SOLUTION:")
        print(f"Day: {selected_day}")
        print(f"Start Time: {start_hh:02d}:{start_mm:02d}")
        print(f"End Time: {end_hh:02d}:{end_mm:02d}")
    else:
        print("No solution found")

solve_meeting_scheduling()