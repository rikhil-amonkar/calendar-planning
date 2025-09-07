from z3 import *

# Define the busy intervals for each participant on each day
Monday_Arthur = [
    (11 * 60, 11 * 60 + 30),  # 11:00-11:30
    (13 * 60 + 30, 14 * 60),  # 13:30-14:00
    (15 * 60, 15 * 60 + 30)   # 15:00-15:30
]
Monday_Michael = [
    (9 * 60, 12 * 60),          # 9:00-12:00
    (12 * 60 + 30, 13 * 60),    # 12:30-13:00
    (14 * 60, 14 * 60 + 30),    # 14:00-14:30
    (15 * 60, 17 * 60)          # 15:00-17:00
]
Wednesday_Arthur = [
    (10 * 60, 10 * 60 + 30),   # 10:00-10:30
    (11 * 60, 11 * 60 + 30),   # 11:00-11:30
    (12 * 60, 12 * 60 + 30),   # 12:00-12:30
    (14 * 60, 14 * 60 + 30),   # 14:00-14:30
    (16 * 60, 16 * 60 + 30)    # 16:00-16:30
]
Wednesday_Michael = [
    (10 * 60, 12 * 60 + 30),   # 10:00-12:30
    (13 * 60, 13 * 60 + 30)    # 13:00-13:30
]

# Create the solver and variables
solver = Optimize()
day = Int('day')
start = Int('start')

# Day must be 0 (Monday) or 1 (Wednesday)
solver.add(Or(day == 0, day == 1))

# Start time must be between 9:00 (540) and 17:00 - 30 mins (990)
solver.add(And(start >= 540, start <= 990))

# Add constraints for Monday's busy intervals
for s, e in Monday_Arthur:
    solver.add(Implies(day == 0, Or(start + 30 <= s, e <= start)))
for s, e in Monday_Michael:
    solver.add(Implies(day == 0, Or(start + 30 <= s, e <= start)))

# Add constraints for Wednesday's busy intervals
for s, e in Wednesday_Arthur:
    solver.add(Implies(day == 1, Or(start + 30 <= s, e <= start)))
for s, e in Wednesday_Michael:
    solver.add(Implies(day == 1, Or(start + 30 <= s, e <= start)))

# Minimize day first, then start time
solver.minimize(day)
solver.minimize(start)

# Check for solution
if solver.check() == sat:
    model = solver.model()
    day_val = model[day].as_long()
    start_val = model[start].as_long()
    day_name = "Monday" if day_val == 0 else "Wednesday"
    
    # Convert start and end times to HH:MM format
    start_h, start_m = divmod(start_val, 60)
    end_val = start_val + 30
    end_h, end_m = divmod(end_val, 60)
    
    time_str = f"{start_h:02d}:{start_m:02d}:{end_h:02d}:{end_m:02d}"
    print(f"{time_str} {day_name}")
else:
    print("No solution found")