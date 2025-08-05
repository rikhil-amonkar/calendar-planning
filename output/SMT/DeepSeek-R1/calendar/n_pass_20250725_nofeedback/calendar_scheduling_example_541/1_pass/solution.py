from z3 import *

def time_to_minutes(time_str):
    parts = time_str.split(':')
    hour = int(parts[0])
    minute = int(parts[1])
    return (hour - 9) * 60 + minute

kayla_blocks = [
    ("10:00", "10:30"),
    ("14:30", "16:00")
]

rebecca_blocks = [
    ("9:00", "13:00"),
    ("13:30", "15:00"),
    ("15:30", "16:00")
]

kayla_intervals = [(time_to_minutes(start), time_to_minutes(end)) for start, end in kayla_blocks]
rebecca_intervals = [(time_to_minutes(start), time_to_minutes(end)) for start, end in rebecca_blocks]

S = Int('S')
solver = Solver()

solver.add(S >= 0)
solver.add(S + 60 <= 480)

for (a, b) in kayla_intervals:
    solver.add(Or(S + 60 <= a, S >= b))

for (a, b) in rebecca_intervals:
    solver.add(Or(S + 60 <= a, S >= b))

if solver.check() == sat:
    model = solver.model()
    start_minutes = model[S].as_long()
    total_minutes = start_minutes
    hours = total_minutes // 60
    minutes = total_minutes % 60
    start_time = f"{9 + hours}:{minutes:02d}"
    end_minutes = start_minutes + 60
    end_hours = 9 + end_minutes // 60
    end_minutes_remainder = end_minutes % 60
    end_time = f"{end_hours}:{end_minutes_remainder:02d}"
    print("Day: Monday")
    print(f"Start Time: {start_time}")
    print(f"End Time: {end_time}")
else:
    print("No solution found")