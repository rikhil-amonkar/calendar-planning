import z3

solver = z3.Solver()

start = z3.Int('start')

# Work hours on Monday: 9:00 (540) to 17:00 (1020)
# Meeting duration 30 mins

# Constraints for Evelyn: end time <= 13:00 (780) => start + 30 <= 780 => start <= 750
solver.add(start >= 540)
solver.add(start <= 750)

# Randy's constraints: avoid his busy times
# Busy1: 9:00-10:30 (540-630)
solver.add(z3.Or(start + 30 <= 540, start >= 630))

# Busy2: 11:00-15:30 (660-930)
solver.add(z3.Or(start + 30 <= 660, start >= 930))

# Busy3: 16:00-17:00 (960-1020)
solver.add(z3.Or(start + 30 <= 960, start >= 1020))

if solver.check() == z3.sat:
    model = solver.model()
    start_time = model[start].as_long()
    day = "Monday"
    # Convert start and end times to HH:MM
    def to_time(m):
        h = m // 60
        m = m % 60
        return f"{h:02d}:{m:02d}"
    start_str = to_time(start_time)
    end_str = to_time(start_time + 30)
    print(f"{{{start_str}:{end_str}}} {day}")
else:
    print("No solution found.")