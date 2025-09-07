from z3 import *

def to_hhmm(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

s = Solver()

day = Int('day')
start = Int('start')

s.add(Or(day == 0, day == 1))
s.add(And(start >= 540, start <= 960))

# Russell's constraints
s.add(Implies(day == 0, Or(start + 60 <= 630, start >= 660)))
s.add(Implies(day == 1, Or(start + 60 <= 780, start >= 810)))

# Alexander's constraints for Monday
s.add(Implies(day == 0, Or(start + 60 <= 540, start >= 690)))
s.add(Implies(day == 0, Or(start + 60 <= 720, start >= 870)))
s.add(Implies(day == 0, Or(start + 60 <= 900, start >= 1020)))

# Alexander's constraints for Tuesday
s.add(Implies(day == 1, Or(start + 60 <= 540, start >= 600)))
s.add(Implies(day == 1, Or(start + 60 <= 780, start >= 840)))
s.add(Implies(day == 1, Or(start + 60 <= 900, start >= 930)))
s.add(Implies(day == 1, Or(start + 60 <= 960, start >= 990)))

# Russell's preference
s.add(Implies(day == 1, start >= 810))

if s.check() == sat:
    m = s.model()
    day_val = m[day].as_long()
    start_val = m[start].as_long()
    end_val = start_val + 60
    day_str = "Monday" if day_val == 0 else "Tuesday"
    start_time = to_hhmm(start_val)
    end_time = to_hhmm(end_val)
    print(f"{day_str} {start_time}:{end_time}")
else:
    print("No solution")