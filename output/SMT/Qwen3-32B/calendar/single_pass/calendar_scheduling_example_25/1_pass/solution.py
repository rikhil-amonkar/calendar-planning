from z3 import *

def min_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

solver = Solver()
S = Int('S')

# Work hours from 9:00 (540) to 17:00 (1020)
solver.add(S >= 540, S <= 960)  # Since meeting is 60 min, S can't exceed 960 (960+60=1020)

# Pamela's constraint: end time <= 14:30 (870 min)
solver.add(S + 60 <= 870)

# Existing busy intervals
anthony = [(570, 600), (720, 780), (960, 990)]
pamela = [(570, 600), (990, 1020)]
zachary = [(540, 690), (720, 750), (780, 810), (870, 900), (960, 1020)]

all_intervals = anthony + pamela + zachary

for start, end in all_intervals:
    solver.add(Or(S + 60 <= start, S >= end))

if solver.check() == sat:
    model = solver.model()
    s_val = model[S].as_long()
    start_time = s_val
    end_time = s_val + 60
    print("SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {min_to_time(start_time)}")
    print(f"End Time: {min_to_time(end_time)}")
else:
    print("No solution found.")