from z3 import *

# Define the start time variable
S = Int('S')

solver = Solver()

# Add constraints for S to be within 9:00 (540) to 16:00 (960) since meeting is 1h
solver.add(S >= 540)
solver.add(S <= 960)

# Julie's blocked intervals (in minutes since midnight)
julie_blocked = [
    (540, 570),  # 9:00-9:30
    (660, 690),  # 11:00-11:30
    (720, 750),  # 12:00-12:30
    (810, 840),  # 13:30-14:00
    (960, 1020)  # 16:00-17:00
]

# Sean's blocked intervals
sean_blocked = [
    (540, 570),  # 9:00-9:30
    (780, 810),  # 13:00-13:30
    (900, 930),  # 15:00-15:30
    (960, 990)   # 16:00-16:30
]

# Lori's blocked intervals
lori_blocked = [
    (600, 630),  # 10:00-10:30
    (660, 780),  # 11:00-13:00
    (930, 1020)  # 15:30-17:00
]

# Add constraints for Julie's blocked intervals
for b_start, b_end in julie_blocked:
    solver.add(Or(S + 60 <= b_start, S >= b_end))

# Add constraints for Sean's blocked intervals
for b_start, b_end in sean_blocked:
    solver.add(Or(S + 60 <= b_start, S >= b_end))

# Add constraints for Lori's blocked intervals
for b_start, b_end in lori_blocked:
    solver.add(Or(S + 60 <= b_start, S >= b_end))

# Check if a solution exists
if solver.check() == sat:
    model = solver.model()
    start = model[S].as_long()
    end = start + 60
    
    # Convert minutes to HH:MM format
    def to_time(mins):
        hours = mins // 60
        minutes = mins % 60
        return f"{hours:02d}:{minutes:02d}"
    
    start_time = to_time(start)
    end_time = to_time(end)
    print(f"Monday {start_time}:{end_time}")
else:
    print("No solution found")