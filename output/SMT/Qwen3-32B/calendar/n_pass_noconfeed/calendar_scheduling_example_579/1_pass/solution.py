import z3

solver = z3.Solver()

s = z3.Int('s')

# Define the time window based on Helen's constraint (must end by 15:00)
solver.add(z3.And(s >= 540, s <= 870))  # 9:00 to 15:00 in minutes

# Christine's busy times
solver.add(z3.Or(s + 30 <= 660, s >= 690))  # 11:00-11:30
solver.add(z3.Or(s + 30 <= 900, s >= 930))  # 15:00-15:30

# Helen's busy times
solver.add(z3.Or(s + 30 <= 570, s >= 630))  # 9:30-10:30
solver.add(z3.Or(s + 30 <= 660, s >= 690))  # 11:00-11:30
solver.add(z3.Or(s + 30 <= 720, s >= 750))  # 12:00-12:30
solver.add(z3.Or(s + 30 <= 810, s >= 960))  # 13:30-16:00

if solver.check() == z3.sat:
    model = solver.model()
    start = model[s].as_long()
    end = start + 30

    def to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"

    start_time = to_time(start)
    end_time = to_time(end)
    print(f"{start_time}:{end_time} Monday")
else:
    print("No solution found")