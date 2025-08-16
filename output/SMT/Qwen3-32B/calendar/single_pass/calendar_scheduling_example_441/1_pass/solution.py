from z3 import *

def to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

solver = Solver()
start = Int('start')

solver.add(start >= 540)  # 9:00 AM in minutes
solver.add(start <= 990)  # 17:00 - 0.5h = 16:30 (990 minutes)

# Joan's intervals
joan = [(690, 720), (870, 900)]
for s, e in joan:
    solver.add(Or(start >= e, s >= start + 30))

# Megan's intervals
megan = [(540, 600), (840, 870), (960, 990)]
for s, e in megan:
    solver.add(Or(start >= e, s >= start + 30))

# Betty's intervals
betty = [(570, 600), (690, 720), (810, 840), (960, 990)]
for s, e in betty:
    solver.add(Or(start >= e, s >= start + 30))

# Judith's intervals
judith = [(540, 660), (720, 780), (840, 900)]
for s, e in judith:
    solver.add(Or(start >= e, s >= start + 30))

# Terry's intervals
terry = [(570, 600), (690, 750), (780, 840), (900, 930), (960, 1020)]
for s, e in terry:
    solver.add(Or(start >= e, s >= start + 30))

# Kathryn's intervals
kathryn = [(570, 600), (630, 660), (690, 780), (840, 960), (990, 1020)]
for s, e in kathryn:
    solver.add(Or(start >= e, s >= start + 30))

if solver.check() == sat:
    model = solver.model()
    start_val = model[start].as_long()
    end_val = start_val + 30
    print("SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {to_time(start_val)}")
    print(f"End Time: {to_time(end_val)}")
else:
    print("No solution found.")