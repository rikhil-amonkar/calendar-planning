from z3 import *

# Initialize the solver
solver = Solver()

# Variables for day (0=Monday, 1=Tuesday) and start time in minutes since midnight
day = Int('day')
start = Int('start')

# Day must be Monday (0) or Tuesday (1)
solver.add(Or(day == 0, day == 1))

# Constraints for Monday
solver.add(Implies(day == 0, And(start >= 540, start + 30 <= 1020)))  # 9:00-17:00

# Harold's Monday busy times: [9:00-10:00, 10:30-17:00]
busy_monday = [(540, 600), (630, 1020)]
for b_start, b_end in busy_monday:
    solver.add(Implies(day == 0, Or(start + 30 <= b_start, start >= b_end)))

# Constraints for Tuesday
solver.add(Implies(day == 1, And(start >= 540, start + 30 <= 1020)))  # 9:00-17:00

# Harold's Tuesday busy times: [9:00-9:30, 10:30-11:30, 12:30-13:30, 14:30-15:30, 16:00-17:00]
busy_tuesday = [(540, 570), (630, 690), (750, 810), (870, 930), (960, 1020)]
for b_start, b_end in busy_tuesday:
    solver.add(Implies(day == 1, Or(start + 30 <= b_start, start >= b_end)))

# Preference constraints: Avoid Monday and prefer Tuesday after 14:30 (870 minutes)
solver.add(Or(day != 0, start >= 870))

# Check for a solution
if solver.check() == sat:
    model = solver.model()
    day_val = model[day].as_long()
    start_val = model[start].as_long()
    end_val = start_val + 30

    # Convert minutes to HH:MM format
    def minutes_to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"

    day_str = "Monday" if day_val == 0 else "Tuesday"
    start_time = minutes_to_time(start_val)
    end_time = minutes_to_time(end_val)
    print(f"{day_str} {start_time}:{end_time}")
else:
    print("No solution found")