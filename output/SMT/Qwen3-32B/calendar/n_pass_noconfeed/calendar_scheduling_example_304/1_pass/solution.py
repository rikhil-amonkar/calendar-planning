from z3 import *

def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

start_time = Int('start_time')
solver = Solver()

# Add time window constraints (9:00 to 17:00 is 540 to 1020 minutes, meeting is 30 min so start must be <= 990)
solver.add(And(start_time >= 540, start_time <= 990))

# Christine's busy times
christine_buses = [(570, 630), (720, 750), (780, 810), (870, 900), (960, 990)]
for s, e in christine_buses:
    solver.add(Or(start_time + 30 <= s, start_time >= e))

# Bobby's busy times
bobby_buses = [(720, 750), (870, 900)]
for s, e in bobby_buses:
    solver.add(Or(start_time + 30 <= s, start_time >= e))

# Elizabeth's busy times
elizabeth_buses = [(540, 570), (690, 780), (780, 840), (900, 930), (960, 1020)]
for s, e in elizabeth_buses:
    solver.add(Or(start_time + 30 <= s, start_time >= e))

# Tyler's busy times
tyler_buses = [(540, 660), (720, 750), (780, 810), (930, 960), (990, 1020)]
for s, e in tyler_buses:
    solver.add(Or(start_time + 30 <= s, start_time >= e))

# Edward's busy times
edward_buses = [(540, 570), (600, 660), (690, 840), (870, 930), (960, 1020)]
for s, e in edward_buses:
    solver.add(Or(start_time + 30 <= s, start_time >= e))

# Janice's preference (soft constraint, not enforced here as per problem statement)
# No hard constraint added for Janice's preference

if solver.check() == sat:
    model = solver.model()
    start = model[start_time].as_long()
    end = start + 30
    day = "Monday"
    print(f"{format_time(start)}:{format_time(end)} {day}")
else:
    print("No solution found")