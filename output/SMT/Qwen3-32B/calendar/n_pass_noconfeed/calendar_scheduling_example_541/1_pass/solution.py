import z3

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Define variables
s = z3.Int('s')
e = s + 60  # meeting duration is 1 hour

solver = z3.Solver()

# Working hours from 9:00 (540) to 17:00 (1020)
solver.add(s >= 540)
solver.add(e <= 1020)

# Kayla's blocked times
# 10:00-10:30 (600-630)
solver.add(z3.Or(e <= 600, s >= 630))
# 14:30-16:00 (870-960)
solver.add(z3.Or(e <= 870, s >= 960))

# Rebecca's blocked times
# 9:00-13:00 (540-780)
solver.add(z3.Or(e <= 540, s >= 780))
# 13:30-15:00 (810-900)
solver.add(z3.Or(e <= 810, s >= 900))
# 15:30-16:00 (930-960)
solver.add(z3.Or(e <= 930, s >= 960))

if solver.check() == z3.sat:
    model = solver.model()
    start = model[s].as_long()
    end = start + 60
    start_time = minutes_to_time(start)
    end_time = minutes_to_time(end)
    print(f"Monday {start_time}:{end_time}")
else:
    print("No solution found")