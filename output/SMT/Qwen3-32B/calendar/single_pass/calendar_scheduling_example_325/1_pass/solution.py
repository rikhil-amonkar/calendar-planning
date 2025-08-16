import z3

solver = z3.Solver()

start = z3.Int('start')

# Define all intervals
intervals = [
    # Jose's intervals
    (660, 690),
    (750, 780),
    # Keith's intervals
    (840, 870),
    (900, 930),
    # Logan's intervals
    (540, 600),
    (720, 750),
    (900, 930),
    # Megan's intervals
    (540, 630),
    (660, 720),
    (780, 810),
    (870, 990),
    # Gary's intervals
    (540, 570),
    (600, 630),
    (690, 780),
    (810, 840),
    (870, 990),
    # Bobby's intervals
    (660, 690),
    (720, 750),
    (780, 960),
]

# Add constraints for start time
solver.add(start >= 540)
solver.add(start <= 900)

# Add constraints for each interval
for s, e in intervals:
    solver.add(z3.Or(start + 30 <= s, start >= e))

if solver.check() == z3.sat:
    model = solver.model()
    start_val = model[start].as_long()
    # Convert to time strings
    start_hours = start_val // 60
    start_minutes = start_val % 60
    start_time = f"{start_hours:02d}:{start_minutes:02d}"
    end_val = start_val + 30
    end_hours = end_val // 60
    end_minutes = end_val % 60
    end_time = f"{end_hours:02d}:{end_minutes:02d}"
    print("SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {start_time}")
    print(f"End Time: {end_time}")
else:
    print("No solution found")