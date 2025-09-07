import z3

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

solver = z3.Solver()

s = z3.Int('s')

# Define the meeting time constraints (9:00 to 17:00, 30-minute meeting)
solver.add(z3.And(s >= 540, s <= 990))

# Patrick's busy times (converted to minutes)
patrick_buses = [(540, 570), (600, 630), (810, 840), (960, 990)]
for start, end in patrick_buses:
    solver.add(z3.Or(s + 30 <= start, s >= end))

# Kayla's busy times
kayla_buses = [(750, 780), (900, 930), (960, 990)]
for start, end in kayla_buses:
    solver.add(z3.Or(s + 30 <= start, s >= end))

# Carl's busy times
carl_buses = [(630, 660), (720, 750), (780, 810), (870, 1020)]
for start, end in carl_buses:
    solver.add(z3.Or(s + 30 <= start, s >= end))

# Christian's busy times
christian_buses = [(540, 750), (780, 840), (870, 1020)]
for start, end in christian_buses:
    solver.add(z3.Or(s + 30 <= start, s >= end))

if solver.check() == z3.sat:
    model = solver.model()
    start_time = model[s].as_long()
    end_time = start_time + 30
    start_str = minutes_to_time(start_time)
    end_str = minutes_to_time(end_time)
    print(f"{{{start_str}:{end_str}}}} Monday")
else:
    print("No solution found.")