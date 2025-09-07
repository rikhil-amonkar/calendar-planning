from z3 import *

solver = Solver()

day = Int('day')
start = Int('start')

# Day must be Monday (0) or Tuesday (1)
solver.add(Or(day == 0, day == 1))

# Start time must be between 9:00 (540) and 16:30 (990)
solver.add(And(start >= 540, start <= 990))

# Monday's busy intervals (Cheryl and Kyle)
monday_intervals = [
    (540, 570),  # Cheryl 9:00-9:30
    (690, 780),  # Cheryl 11:30-13:00
    (930, 960),  # Cheryl 15:30-16:00
    (540, 1020)  # Kyle 9:00-17:00
]

for b_s, b_e in monday_intervals:
    solver.add(Or(day != 0, Or(start + 30 <= b_s, start >= b_e)))

# Tuesday's busy intervals (Cheryl and Kyle)
tuesday_intervals = [
    (900, 930),  # Cheryl 15:00-15:30
    (570, 1020)  # Kyle 9:30-17:00
]

for b_s, b_e in tuesday_intervals:
    solver.add(Or(day != 1, Or(start + 30 <= b_s, start >= b_e)))

if solver.check() == sat:
    model = solver.model()
    day_val = model[day].as_long()
    start_val = model[start].as_long()
    days = ['Monday', 'Tuesday', 'Wednesday']
    day_name = days[day_val]
    start_h = start_val // 60
    start_m = start_val % 60
    end_val = start_val + 30
    end_h = end_val // 60
    end_m = end_val % 60
    start_time = f"{start_h:02d}:{start_m:02d}"
    end_time = f"{end_h:02d}:{end_m:02d}"
    print(f"{day_name} {start_time}:{end_time}")
else:
    print("No solution found")