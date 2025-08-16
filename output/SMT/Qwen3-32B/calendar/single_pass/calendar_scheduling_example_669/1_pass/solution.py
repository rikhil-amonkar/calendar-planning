import z3

# Define solver
solver = z3.Solver()

# Variables
is_monday = z3.Bool('is_monday')
start = z3.Int('start')

# Work hour constraints
solver.add(start >= 540)
solver.add(start <= 990)  # Because start + 30 <= 1020 (17:00)

# Doris's constraints on Monday
doris_monday = z3.Or(
    start == 690,  # 11:30
    z3.And(start >= 750, start <= 780),  # 12:30–13:00
    z3.And(start >= 960, start <= 990)   # 16:00–16:30
)
solver.add(z3.Implies(is_monday, doris_monday))

# Jean's constraints on Tuesday
jean_tuesday = z3.Or(
    z3.And(start >= 540, start <= 660),  # 9:00–11:00
    z3.And(start >= 720, start <= 930)   # 12:00–15:30
)
solver.add(z3.Implies(z3.Not(is_monday), jean_tuesday))

# Preference constraint for Doris
solver.add(start <= 840)  # 14:00

# Solve
if solver.check() == z3.sat:
    model = solver.model()
    day = model[is_monday].as_long()
    start_time = model[start].as_long()
    end_time = start_time + 30

    day_name = "Monday" if day else "Tuesday"

    def to_time_str(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"

    print("SOLUTION:")
    print(f"Day: {day_name}")
    print(f"Start Time: {to_time_str(start_time)}")
    print(f"End Time: {to_time_str(end_time)}")
else:
    print("No solution found.")