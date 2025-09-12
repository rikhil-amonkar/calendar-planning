from z3 import *

def to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

s = Int('s')
solver = Solver()

# Work hours from 9:00 (540) to 17:00 (1020), but meeting must end by 16:00 (960) for Juan
solver.add(And(s >= 540, s <= 930))

# Juan's constraints: busy 9:00-10:30 (540-630), 15:30-16:00 (930-960)
solver.add(Or(s + 30 <= 540, s >= 630))  # First busy interval
solver.add(Or(s + 30 <= 930, s >= 960))  # Second busy interval

# Marilyn's constraints: busy 11:00-11:30 (660-690), 12:30-13:00 (750-780)
solver.add(Or(s + 30 <= 660, s >= 690))  # First busy interval
solver.add(Or(s + 30 <= 750, s >= 780))  # Second busy interval

# Ronald's constraints: busy 9:00-10:30 (540-630), 12:00-12:30 (720-750), 13:00-13:30 (780-810), 14:00-16:30 (840-990)
solver.add(Or(s + 30 <= 540, s >= 630))  # First busy interval
solver.add(Or(s + 30 <= 720, s >= 750))  # Second busy interval
solver.add(Or(s + 30 <= 780, s >= 810))  # Third busy interval
solver.add(Or(s + 30 <= 840, s >= 990))  # Fourth busy interval

if solver.check() == sat:
    model = solver.model()
    start = model[s].as_long()
    end = start + 30
    start_time = to_time(start)
    end_time = to_time(end)
    print(f"Monday {start_time}:{end_time}")
else:
    print("No solution found")