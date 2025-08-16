from z3 import *

solver = Solver()

S = Int('S')

solver.add(S >= 540, S <= 990)
solver.add(S >= 750)  # Roger's preference

busy_intervals = [
    # Kathleen
    (870, 930),
    # Carolyn
    (720, 750),
    (780, 810),
    # Cheryl
    (540, 570),
    (600, 690),
    (750, 810),
    (840, 1020),
    # Virginia
    (570, 690),
    (720, 750),
    (780, 810),
    (870, 930),
    (960, 1020),
    # Angela
    (570, 600),
    (630, 690),
    (720, 750),
    (780, 810),
    (840, 990),
]

for start, end in busy_intervals:
    solver.add(Or(S + 30 <= start, S >= end))

if solver.check() == sat:
    model = solver.model()
    start_time_minutes = model[S].as_long()
    
    def minutes_to_time(m):
        hours = m // 60
        minutes = m % 60
        return f"{hours:02d}:{minutes:02d}"
    
    day = "Monday"
    start_time = minutes_to_time(start_time_minutes)
    end_time = minutes_to_time(start_time_minutes + 30)
    print("SOLUTION:")
    print(f"Day: {day}")
    print(f"Start Time: {start_time}")
    print(f"End Time: {end_time}")
else:
    print("No solution found.")