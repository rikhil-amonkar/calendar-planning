import z3

def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

solver = z3.Solver()
start_time = z3.Int('start_time')

# Define work hours constraints (9:00-17:00, 30-minute meeting)
solver.add(start_time >= 9 * 60)          # 540 minutes (9:00 AM)
solver.add(start_time <= 17 * 60 - 30)    # 990 minutes (16:30 PM)

# Gregory's blocked intervals
greg_blocked = [(9*60, 10*60), (10*60+30, 11*60+30), (12*60+30, 13*60), (13*60+30, 14*60)]
for a, b in greg_blocked:
    solver.add(z3.Or(start_time + 30 <= a, start_time >= b))

# Christine's blocked intervals
christine_blocked = [(9*60, 11*60+30), (13*60+30, 17*60)]
for a, b in christine_blocked:
    solver.add(z3.Or(start_time + 30 <= a, start_time >= b))

# Vincent's blocked intervals
vincent_blocked = [(9*60, 9*60+30), (10*60+30, 12*60), (12*60+30, 14*60), (14*60+30, 17*60)]
for a, b in vincent_blocked:
    solver.add(z3.Or(start_time + 30 <= a, start_time >= b))

if solver.check() == z3.sat:
    model = solver.model()
    start = model[start_time].as_long()
    end = start + 30
    print("SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {to_time_str(start)}")
    print(f"End Time: {to_time_str(end)}")
else:
    print("No solution found.")