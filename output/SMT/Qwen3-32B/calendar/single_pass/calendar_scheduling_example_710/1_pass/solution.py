from z3 import *

def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

solver = Solver()

day = Int('day')
start = Int('start')

# Day must be Monday (0) or Tuesday (1)
solver.add(Or(day == 0, day == 1))

# Start time between 9:00 (540) and 16:30 (990)
solver.add(And(start >= 540, start <= 990))

# Cheryl's busy times
cheril_busy_mon = [(540, 570), (690, 780), (930, 960)]
cheril_busy_tue = [(900, 930)]

for b_start, b_end in cheril_busy_mon:
    solver.add(Or(day != 0, Or(start >= b_end, start + 30 <= b_start)))

for b_start, b_end in cheril_busy_tue:
    solver.add(Or(day != 1, Or(start >= b_end, start + 30 <= b_start)))

# Kyle's busy times
kyle_busy_mon = [(540, 1020)]
kyle_busy_tue = [(570, 1020)]

for b_start, b_end in kyle_busy_mon:
    solver.add(Or(day != 0, Or(start >= b_end, start + 30 <= b_start)))

for b_start, b_end in kyle_busy_tue:
    solver.add(Or(day != 1, Or(start >= b_end, start + 30 <= b_start)))

if solver.check() == sat:
    model = solver.model()
    day_val = model[day].as_long()
    start_val = model[start].as_long()
    end_val = start_val + 30

    days = {0: 'Monday', 1: 'Tuesday'}
    day_name = days[day_val]

    print("SOLUTION:")
    print(f"Day: {day_name}")
    print(f"Start Time: {to_time_str(start_val)}")
    print(f"End Time: {to_time_str(end_val)}")
else:
    print("No solution found.")