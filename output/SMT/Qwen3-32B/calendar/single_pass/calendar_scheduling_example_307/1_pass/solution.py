from z3 import *

solver = Solver()

start = Int('start')

# Define work hours constraints (9:00 to 17:00, 30-minute meeting)
solver.add(start >= 540)  # 9:00 AM
solver.add(start <= 990)  # 16:30 PM (meeting ends at 17:00)

# Define blocked intervals for each participant in minutes since midnight
blocked = {
    'Stephen': [(600, 630), (720, 750)],
    'Brittany': [(660, 690), (810, 840), (930, 960), (990, 1020)],
    'Dorothy': [(540, 570), (600, 630), (660, 750), (780, 900), (930, 1020)],
    'Rebecca': [(570, 630), (660, 690), (720, 750), (780, 1020)],
    'Jordan': [(540, 570), (600, 660), (690, 720), (780, 900), (930, 990)],
    'Ronald': []
}

# Add constraints for each blocked interval
for intervals in blocked.values():
    for (bs, be) in intervals:
        solver.add(Or(start + 30 <= bs, start >= be))

# Check for solution
if solver.check() == sat:
    model = solver.model()
    start_val = model[start].as_long()
    end_val = start_val + 30
    
    # Convert minutes to HH:MM format
    def to_time_str(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"
    
    print("SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {to_time_str(start_val)}")
    print(f"End Time: {to_time_str(end_val)}")
else:
    print("No solution found")