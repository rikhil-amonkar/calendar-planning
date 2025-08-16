import z3

def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

solver = z3.Solver()
start_time = z3.Int('start_time')

# Work hours constraints (9:00 to 17:00, 30 min meeting => start <= 16:30)
solver.add(start_time >= 9 * 60)  # 9:00
solver.add(start_time <= 16 * 60 + 30)  # 16:30

# Nicole's existing schedule constraints
# Avoid 9:00-10:00 (540-600) and 10:30-16:30 (630-990)
solver.add(z3.And(
    start_time >= 10 * 60,  # 10:00 (after first meeting)
    z3.Or(
        start_time <= 10 * 60,  # Before 10:30 (end by 10:30)
        start_time >= 16 * 60 + 30  # After 16:30 (start at 16:30)
    )
))

# Nicole's preference: not before 16:00
solver.add(start_time >= 16 * 60)

if solver.check() == z3.sat:
    model = solver.model()
    start = model[start_time].as_long()
    end = start + 30
    print("SOLUTION:")
    print("Day: Monday")
    print(f"Start Time: {format_time(start)}")
    print(f"End Time: {format_time(end)}")
else:
    print("No solution found")