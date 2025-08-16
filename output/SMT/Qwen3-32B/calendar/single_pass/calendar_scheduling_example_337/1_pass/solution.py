import z3

def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

solver = z3.Solver()
S = z3.Int('S')

# Define work hours (9:00 to 17:00 in minutes since midnight)
solver.add(z3.And(S >= 540, S <= 990))  # 9:00 (540) to 16:30 (990) for 30-min meeting

# Collect all busy intervals
all_busy = []

# John's busy times
all_busy.extend([(690, 720), (840, 870)])

# Megan's busy times
all_busy.extend([(720, 750), (840, 900), (930, 960)])

# Brandon has no meetings

# Kimberly's busy times
all_busy.extend([(540, 570), (600, 630), (660, 870), (900, 960), (990, 1020)])

# Sean's busy times
all_busy.extend([(600, 660), (690, 840), (900, 930)])

# Lori's busy times
all_busy.extend([(540, 570), (630, 720), (780, 870), (960, 990)])

# Add constraints for all busy intervals
for start, end in all_busy:
    solver.add(z3.Or(S >= end, start >= S + 30))

if solver.check() == z3.sat:
    model = solver.model()
    start_time = model[S].as_long()
    end_time = start_time + 30
    print("SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {to_time_str(start_time)}")
    print(f"End Time: {to_time_str(end_time)}")
else:
    print("No solution found.")