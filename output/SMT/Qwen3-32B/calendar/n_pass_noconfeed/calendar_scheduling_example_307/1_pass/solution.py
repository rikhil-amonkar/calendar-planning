import z3

def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

solver = z3.Solver()

start_time = z3.Int('start_time')

# Define work hours (9:00 AM to 5:00 PM)
solver.add(start_time >= 9 * 60)  # 540
solver.add(start_time <= 17 * 60 - 30)  # 990

# Blocked intervals for each participant (converted to minutes)
blocked_intervals = {
    'Stephen': [(10 * 60, 10 * 60 + 30), (12 * 60, 12 * 60 + 30)],
    'Brittany': [(11 * 60, 11 * 60 + 30), (13 * 60 + 30, 14 * 60), (15 * 60 + 30, 16 * 60), (16 * 60 + 30, 17 * 60)],
    'Dorothy': [(9 * 60, 9 * 60 + 30), (10 * 60, 10 * 60 + 30), (11 * 60, 12 * 60 + 30), (13 * 60, 15 * 60), (15 * 60 + 30, 17 * 60)],
    'Rebecca': [(9 * 60 + 30, 10 * 60 + 30), (11 * 60, 11 * 60 + 30), (12 * 60, 12 * 60 + 30), (13 * 60, 17 * 60)],
    'Jordan': [(9 * 60, 9 * 60 + 30), (10 * 60, 11 * 60), (11 * 60 + 30, 12 * 60), (13 * 60, 15 * 60), (15 * 60 + 30, 16 * 60 + 30)]
}

for person in blocked_intervals:
    for s, e in blocked_intervals[person]:
        solver.add(z3.Or(start_time + 30 <= s, start_time >= e))

if solver.check() == z3.sat:
    model = solver.model()
    start = model[start_time].as_long()
    end = start + 30
    start_str = to_time_str(start)
    end_str = to_time_str(end)
    print(f"{{{start_str}:{end_str}}} Monday")
else:
    print("No solution found")