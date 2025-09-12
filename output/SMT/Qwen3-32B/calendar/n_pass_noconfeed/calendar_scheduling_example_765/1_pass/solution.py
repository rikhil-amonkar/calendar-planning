from z3 import *

s = Solver()

day = Int('day')
start = Int('start')

s.add(Or(day == 0, day == 1, day == 2))
s.add(And(0 <= start, start <= 450))

# Monday constraints
monday_joshua = [(360, 390)]
monday_joyce = [(0, 30), (60, 120), (150, 210), (240, 360), (390, 480)]

monday_joshua_constraints = True
for b_start, b_end in monday_joshua:
    monday_joshua_constraints = And(monday_joshua_constraints, Or(start + 30 <= b_start, start >= b_end))

monday_joyce_constraints = True
for b_start, b_end in monday_joyce:
    monday_joyce_constraints = And(monday_joyce_constraints, Or(start + 30 <= b_start, start >= b_end))

monday_all = And(monday_joshua_constraints, monday_joyce_constraints, start >= 180)
s.add(Implies(day == 0, monday_all))

# Tuesday constraints
tuesday_joshua = [(150, 180), (240, 270), (330, 360)]
tuesday_joyce = [(0, 480)]

tuesday_joshua_constraints = True
for b_start, b_end in tuesday_joshua:
    tuesday_joshua_constraints = And(tuesday_joshua_constraints, Or(start + 30 <= b_start, start >= b_end))

tuesday_joyce_constraints = True
for b_start, b_end in tuesday_joyce:
    tuesday_joyce_constraints = And(tuesday_joyce_constraints, Or(start + 30 <= b_start, start >= b_end))

tuesday_all = And(tuesday_joshua_constraints, tuesday_joyce_constraints)
s.add(Implies(day == 1, tuesday_all))

# Wednesday constraints
wednesday_joshua = []
wednesday_joyce = [(0, 30), (60, 120), (210, 390), (420, 450)]

wednesday_joshua_constraints = True
for b_start, b_end in wednesday_joshua:
    wednesday_joshua_constraints = And(wednesday_joshua_constraints, Or(start + 30 <= b_start, start >= b_end))

wednesday_joyce_constraints = True
for b_start, b_end in wednesday_joyce:
    wednesday_joyce_constraints = And(wednesday_joyce_constraints, Or(start + 30 <= b_start, start >= b_end))

wednesday_all = And(wednesday_joshua_constraints, wednesday_joyce_constraints)
s.add(Implies(day == 2, wednesday_all))

if s.check() == sat:
    m = s.model()
    day_val = m[day].as_long()
    start_val = m[start].as_long()
    days = ['Monday', 'Tuesday', 'Wednesday']
    day_name = days[day_val]

    start_minutes_since_midnight = 9 * 60 + start_val
    end_minutes_since_midnight = start_minutes_since_midnight + 30

    start_h = start_minutes_since_midnight // 60
    start_m = start_minutes_since_midnight % 60
    end_h = end_minutes_since_midnight // 60
    end_m = end_minutes_since_midnight % 60

    time_range = f"{start_h:02d}:{start_m:02d}:{end_h:02d}:{end_m:02d}"
    print(f"{day_name} {time_range}")
else:
    print("No solution")