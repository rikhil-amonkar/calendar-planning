from z3 import *

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

solver = Optimize()

day = Int('day')
start = Int('start')
end = Int('end')

solver.add(And(day >= 0, day <= 3))
solver.add(And(start >= 540, start <= 990))
solver.add(end == start + 30)

# Mary's busy times
mary_busy = {
    1: [(600, 630), (930, 960)],
    2: [(570, 600), (900, 930)],
    3: [(540, 600), (630, 690)],
}

# Alexis's busy times
alexis_busy = {
    0: [(540, 600), (630, 720), (750, 990)],
    1: [(540, 600), (630, 690), (720, 930), (960, 1020)],
    2: [(540, 660), (690, 1020)],
    3: [(600, 720), (840, 870), (930, 960), (990, 1020)],
}

# Add constraints for Mary's busy times
for d, intervals in mary_busy.items():
    for b_start, b_end in intervals:
        solver.add(Implies(day == d, Or(end <= b_start, start >= b_end)))

# Add constraints for Alexis's busy times
for d, intervals in alexis_busy.items():
    for b_start, b_end in intervals:
        solver.add(Implies(day == d, Or(end <= b_start, start >= b_end)))

# Minimize the start time
solver.minimize(start)

if solver.check() == sat:
    model = solver.model()
    day_val = model[day].as_long()
    start_val = model[start].as_long()
    end_val = model[end].as_long()
    # Map day to name
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']
    day_name = days[day_val]
    print("SOLUTION:")
    print(f"Day: {day_name}")
    print(f"Start Time: {minutes_to_time(start_val)}")
    print(f"End Time: {minutes_to_time(end_val)}")
else:
    print("No solution found.")