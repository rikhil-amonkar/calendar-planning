import z3

solver = z3.Solver()

is_monday = z3.Bool('is_monday')
start_time = z3.Int('start_time')

# Time constraints (9:00-17:00, 30 min meeting)
solver.add(start_time >= 540)  # 9:00 AM
solver.add(start_time <= 990)  # 17:00 - 30 min = 16:30 (990)

# Monday constraints for Jesse and Lawrence
busy_jesse_monday = [(810, 840), (870, 900)]  # 13:30-14:00, 14:30-15:00
for s, e in busy_jesse_monday:
    solver.add(z3.Implies(is_monday, z3.Or(start_time + 30 <= s, start_time >= e)))

# Lawrence is busy all day on Monday from 9:00 to 17:00
s, e = 540, 1020
solver.add(z3.Implies(is_monday, z3.Or(start_time + 30 <= s, start_time >= e)))

# Tuesday constraints
# Lawrence can't meet after 16:30 (990 minutes), so meeting must end by 16:30
# start_time + 30 <= 990 → start_time <= 960
solver.add(z3.Implies(z3.Not(is_monday), start_time <= 960))

# Jesse's Tuesday busy times
busy_jesse_tuesday = [(540, 570), (780, 810), (840, 900)]  # 9:00-9:30, 13:00-13:30, 14:00-15:00
for s, e in busy_jesse_tuesday:
    solver.add(z3.Implies(z3.Not(is_monday), z3.Or(start_time + 30 <= s, start_time >= e)))

# Lawrence's Tuesday busy times
busy_lawrence_tuesday = [(570, 630), (690, 750), (780, 810), (870, 900), (930, 990)]
for s, e in busy_lawrence_tuesday:
    solver.add(z3.Implies(z3.Not(is_monday), z3.Or(start_time + 30 <= s, start_time >= e)))

if solver.check() == z3.sat:
    model = solver.model()
    day = "Monday" if model.evaluate(is_monday) else "Tuesday"
    start_val = model[start_time].as_long()
    end_val = start_val + 30

    def to_hhmm(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"

    start_str = to_hhmm(start_val)
    end_str = to_hhmm(end_val)
    print(f"{day} {start_str}:{end_str}")
else:
    print("No solution found.")