import z3

solver = z3.Solver()

S = z3.Int('S')

# Work hours from 9:00 (540 min) to 17:00 (1020 min), meeting is 60 min
solver.add(S >= 9 * 60)  # 540 minutes (9:00 AM)
solver.add(S <= 16 * 60)  # 960 minutes (4:00 PM) to allow for 1-hour meeting until 5:00 PM

# Kayla's busy times
# 10:00-10:30 (600-630)
solver.add(z3.Or(S + 60 <= 600, S >= 630))
# 14:30-16:00 (870-960)
solver.add(z3.Or(S + 60 <= 870, S >= 960))

# Rebecca's busy times
# 9:00-13:00 (540-780)
solver.add(z3.Or(S + 60 <= 540, S >= 780))
# 13:30-15:00 (810-900)
solver.add(z3.Or(S + 60 <= 810, S >= 900))
# 15:30-16:00 (930-960)
solver.add(z3.Or(S + 60 <= 930, S >= 960))

if solver.check() == z3.sat:
    model = solver.model()
    start_min = model[S].as_long()
    day = "Monday"
    start_time = f"{start_min // 60:02d}:{start_min % 60:02d}"
    end_min = start_min + 60
    end_time = f"{end_min // 60:02d}:{end_min % 60:02d}"
    print(f"SOLUTION:\nDay: {day}\nStart Time: {start_time}\nEnd Time: {end_time}")
else:
    print("No solution found.")