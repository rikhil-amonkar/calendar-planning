from z3 import *

def schedule_meeting():
    day = Int('day')
    start = Int('start')

    s = Solver()

    # Day must be 0 (Monday) or 1 (Tuesday)
    s.add(Or(day == 0, day == 1))

    # Start time between 9:00 (540) and 17:00 (1020), with one hour meeting
    s.add(start >= 540)
    s.add(start + 60 <= 1020)

    # Russell's constraints
    # Monday: 10:30-11:00 (630-660)
    s.add(Implies(day == 0, Or(start + 60 <= 630, 660 <= start)))
    # Tuesday: 13:00-13:30 (780-810)
    s.add(Implies(day == 1, Or(start + 60 <= 780, 810 <= start)))
    # Russell's preference: if Tuesday, start >= 13:30 (810)
    s.add(Implies(day == 1, start >= 810))

    # Alexander's constraints
    # Monday's busy intervals
    # 9:00-11:30 (540-690)
    s.add(Implies(day == 0, Or(start + 60 <= 540, 690 <= start)))
    # 12:00-14:30 (720-870)
    s.add(Implies(day == 0, Or(start + 60 <= 720, 870 <= start)))
    # 15:00-17:00 (900-1020)
    s.add(Implies(day == 0, Or(start + 60 <= 900, 1020 <= start)))

    # Tuesday's busy intervals
    # 9:00-10:00 (540-600)
    s.add(Implies(day == 1, Or(start + 60 <= 540, 600 <= start)))
    # 13:00-14:00 (780-840)
    s.add(Implies(day == 1, Or(start + 60 <= 780, 840 <= start)))
    # 15:00-15:30 (900-930)
    s.add(Implies(day == 1, Or(start + 60 <= 900, 930 <= start)))
    # 16:00-16:30 (960-990)
    s.add(Implies(day == 1, Or(start + 60 <= 960, 990 <= start)))

    if s.check() == sat:
        m = s.model()
        day_val = m[day].as_long()
        start_val = m[start].as_long()
        end_val = start_val + 60

        # Convert to day name
        day_name = "Monday" if day_val == 0 else "Tuesday"

        # Convert start and end times to HH:MM format
        def to_time(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{hours:02d}:{mins:02d}"

        start_time = to_time(start_val)
        end_time = to_time(end_val)

        print("SOLUTION:")
        print(f"Day: {day_name}")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found.")

schedule_meeting()