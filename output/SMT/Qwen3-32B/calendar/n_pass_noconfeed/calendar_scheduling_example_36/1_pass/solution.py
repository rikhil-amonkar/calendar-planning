import z3

def to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

s = z3.Int('s')
solver = z3.Solver()

# Meeting must be between 9:00 (540) and 17:00 (1020), one hour long
solver.add(s >= 540)
solver.add(s + 60 <= 1020)

# Denise's end time constraint: end by 12:30 (750)
solver.add(s + 60 <= 750)

# Ryan's constraints
# Busy 9:00-9:30 (540-570)
solver.add(z3.Or(s + 60 <= 540, s >= 570))
# Busy 12:30-13:00 (750-780)
solver.add(z3.Or(s + 60 <= 750, s >= 780))

# Denise's constraints
# Busy 9:30-10:30 (570-630)
solver.add(z3.Or(s + 60 <= 570, s >= 630))
# Busy 12:00-13:00 (720-780)
solver.add(z3.Or(s + 60 <= 720, s >= 780))

if solver.check() == z3.sat:
    model = solver.model()
    start = model[s].as_long()
    end = start + 60
    start_time = to_time(start)
    end_time = to_time(end)
    print(f"{{{start_time}:{end_time}}} Monday")
else:
    print("No solution found")