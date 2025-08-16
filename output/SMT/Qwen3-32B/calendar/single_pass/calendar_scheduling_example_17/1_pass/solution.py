from z3 import *

solver = Solver()

start = Int('start')

# Main constraints for the meeting time
solver.add(start >= 540)  # 9:00 AM
solver.add(start <= 780)  # 13:00 PM (meeting ends at 13:30)

# Margaret's blocked intervals (in minutes since midnight)
margaret_blocked = [
    (540, 600),   # 9:00-10:00
    (630, 660),   # 10:30-11:00
    (690, 720),   # 11:30-12:00
    (780, 810),   # 13:00-13:30
    (900, 930)    # 15:00-15:30
]

for s, e in margaret_blocked:
    solver.add(Or(start + 30 <= s, start >= e))

# Donna's blocked intervals
donna_blocked = [
    (870, 900),   # 14:30-15:00
    (960, 990)    # 16:00-16:30
]

for s, e in donna_blocked:
    solver.add(Or(start + 30 <= s, start >= e))

# Helen's blocked intervals
helen_blocked = [
    (540, 570),   # 9:00-9:30
    (600, 690),   # 10:00-11:30
    (780, 840)    # 13:00-14:00
]

for s, e in helen_blocked:
    solver.add(Or(start + 30 <= s, start >= e))

if solver.check() == sat:
    model = solver.model()
    start_val = model[start].as_long()
    end_val = start_val + 30
    
    # Convert minutes to HH:MM format
    def to_time_str(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"
    
    start_time = to_time_str(start_val)
    end_time = to_time_str(end_val)
    
    print("SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {start_time}")
    print(f"End Time: {end_time}")
else:
    print("No solution found")