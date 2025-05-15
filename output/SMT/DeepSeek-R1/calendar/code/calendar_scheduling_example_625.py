import z3

solver = z3.Solver()
S = z3.Int('S')

# Work hours: Monday 9:00 (0) to Tuesday 17:00 (960 minutes)
solver.add(z3.Or(
    z3.And(S >= 0, S + 30 <= 480),   # Monday
    z3.And(S >= 480, S + 30 <= 960)  # Tuesday
))

# Harold's preferences: avoid Monday and Tuesday before 14:30 (810 minutes from Monday 9:00)
solver.add(S >= 810)  # Forces Tuesday after 14:30

# Harold's blocked intervals (minutes since Monday 9:00)
harold_blocks = [
    (0, 60), (90, 480),              # Monday
    (480, 510), (570, 630), (690, 750), (810, 870), (900, 960)  # Tuesday
]

for start, end in harold_blocks:
    solver.add(z3.Or(S + 30 <= start, S >= end))

if solver.check() == z3.sat:
    model = solver.model()
    start_total = model[S].as_long()
    day = "Monday" if start_total < 480 else "Tuesday"
    start_on_day = start_total - (480 if day == "Tuesday" else 0)
    start_h = 9 + start_on_day // 60
    start_m = start_on_day % 60
    end_on_day = start_on_day + 30
    end_h = 9 + end_on_day // 60
    end_m = end_on_day % 60
    print(f"{day}\n{start_h}:{start_m:02d}\n{end_h}:{end_m:02d}")
else:
    print("No solution found")