import z3

def minutes_to_time(m):
    hours = m // 60
    mins = m % 60
    return f"{hours:02d}:{mins:02d}"

solver = z3.Solver()

S = z3.Int('S')

# Work hours from 9:00 (540) to 17:00 (1020). Meeting duration is 30 minutes.
# Therefore, S must be between 540 and 990 (inclusive).
solver.add(S >= 540)
solver.add(S <= 990)

# Megan's constraint: meeting starts at 10:00 (600) or later.
solver.add(S >= 600)

# Kimberly's busy intervals in minutes since midnight.
kimberly_buses = [(600, 630), (660, 720), (960, 990)]
for start, end in kimberly_buses:
    solver.add(z3.Or(S + 30 <= start, S >= end))

# Marie's busy intervals.
marie_buses = [(600, 660), (690, 900), (960, 990)]
for start, end in marie_buses:
    solver.add(z3.Or(S + 30 <= start, S >= end))

# Diana's busy intervals.
diana_buses = [(570, 600), (630, 870), (930, 1020)]
for start, end in diana_buses:
    solver.add(z3.Or(S + 30 <= start, S >= end))

if solver.check() == z3.sat:
    model = solver.model()
    S_val = model[S].as_long()
    start_time = minutes_to_time(S_val)
    end_time = minutes_to_time(S_val + 30)
    print(f"{start_time}:{end_time} Monday")
else:
    print("No solution found")