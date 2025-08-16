from z3 import *

def solve_meeting():
    s = Solver()
    day = Int('day')
    start_time = Int('start_time')
    s.add(And(day >= 0, day <= 2))
    s.add(And(start_time >= 9*60, start_time <= 16*60))

    # Martha's constraints
    s.add(Implies(day == 0, Or(start_time + 60 <= 960, start_time >= 1020)))
    s.add(Implies(day == 1, Or(start_time + 60 <= 900, start_time >= 930)))
    s.add(Implies(day == 2, Or(start_time + 60 <= 600, start_time >= 660)))
    s.add(Implies(day == 2, Or(start_time + 60 <= 840, start_time >= 870)))

    # Beverly's constraints
    s.add(Implies(day == 0, Or(start_time + 60 <= 540, start_time >= 810)))
    s.add(Implies(day == 0, Or(start_time + 60 <= 840, start_time >= 1020)))
    s.add(Implies(day == 1, Or(start_time + 60 <= 540, start_time >= 1020)))
    s.add(Implies(day == 2, Or(start_time + 60 <= 570, start_time >= 930)))
    s.add(Implies(day == 2, Or(start_time + 60 <= 990, start_time >= 1020)))

    if s.check() == sat:
        m = s.model()
        day_val = m[day].as_long()
        start_val = m[start_time].as_long()
        end_val = start_val + 60
        days = ['Monday', 'Tuesday', 'Wednesday']
        def to_time(mins):
            hours = mins // 60
            minutes = mins % 60
            return f"{hours:02d}:{minutes:02d}"
        print("SOLUTION:")
        print(f"Day: {days[day_val]}")
        print(f"Start Time: {to_time(start_val)}")
        print(f"End Time: {to_time(end_val)}")
    else:
        print("No solution found.")

solve_meeting()