from z3 import *

def solve_meeting_schedule():
    # Create the solver
    s = Solver()

    # Define the possible days
    days = ['Monday', 'Tuesday', 'Wednesday']
    day = Int('day')
    s.add(day >= 0, day <= 2)  # 0: Monday, 1: Tuesday, 2: Wednesday

    # Define start and end times in minutes from 9:00 (540 minutes)
    start_time = Int('start_time')
    end_time = Int('end_time')
    meeting_duration = 30  # minutes

    # Work hours: 9:00 to 17:00 (540 to 1020 minutes)
    s.add(start_time >= 540, end_time <= 1020)
    s.add(end_time == start_time + meeting_duration)

    # Jennifer's busy times in minutes from 9:00
    # Monday: 9:00-11:00 (540-660), 11:30-13:00 (690-780), 13:30-14:30 (810-870), 15:00-17:00 (900-1020)
    # Tuesday: 9:00-11:30 (540-690), 12:00-17:00 (720-1020)
    # Wednesday: 9:00-11:30 (540-690), 12:00-12:30 (720-750), 13:00-14:00 (780-840), 14:30-16:00 (870-960), 16:30-17:00 (990-1020)

    # Constraints for Jennifer's busy times
    def add_jennifer_busy_constraints(d, start, end):
        # If the day is d, the meeting cannot overlap with the busy interval [start, end]
        s.add(Not(And(day == d, start_time < end, end_time > start)))

    # Monday
    add_jennifer_busy_constraints(0, 540, 660)
    add_jennifer_busy_constraints(0, 690, 780)
    add_jennifer_busy_constraints(0, 810, 870)
    add_jennifer_busy_constraints(0, 900, 1020)

    # Tuesday
    add_jennifer_busy_constraints(1, 540, 690)
    add_jennifer_busy_constraints(1, 720, 1020)

    # Wednesday
    add_jennifer_busy_constraints(2, 540, 690)
    add_jennifer_busy_constraints(2, 720, 750)
    add_jennifer_busy_constraints(2, 780, 840)
    add_jennifer_busy_constraints(2, 870, 960)
    add_jennifer_busy_constraints(2, 990, 1020)

    # John's preferences: avoid Monday after 14:30 (870 minutes), Tuesday, Wednesday
    # So prefer Monday before 14:30, but since John has no meetings, we can ignore his preferences if necessary
    # But we'll try to find a time that fits Jennifer's schedule first

    # Check for a solution
    if s.check() == sat:
        m = s.model()
        day_idx = m[day].as_long()
        start = m[start_time].as_long()
        end = m[end_time].as_long()

        # Convert minutes back to HH:MM
        def minutes_to_time(minutes):
            h = minutes // 60
            m = minutes % 60
            return f"{h:02d}:{m:02d}"

        start_str = minutes_to_time(start)
        end_str = minutes_to_time(end)
        day_str = days[day_idx]

        print(f"SOLUTION:")
        print(f"Day: {day_str}")
        print(f"Start Time: {start_str}")
        print(f"End Time: {end_str}")
    else:
        print("No solution found")

solve_meeting_schedule()