import z3

solver = z3.Solver()

# Define the start time in minutes since midnight
S = z3.Int('S')

# Meeting is 30 minutes long, between 9:00 (540) and 17:00 (1020)
solver.add(S >= 540)
solver.add(S <= 1020 - 30)  # 990

# Michael's blocked intervals
michael_intervals = [
    (570, 630),  # 9:30-10:30
    (900, 930),  # 15:00-15:30
    (960, 990),  # 16:00-16:30
]

for start, end in michael_intervals:
    solver.add(z3.Or(S + 30 <= start, S >= end))

# Arthur's blocked intervals
arthur_intervals = [
    (540, 720),   # 9:00-12:00
    (780, 900),   # 13:00-15:00
    (930, 960),   # 15:30-16:00
    (990, 1020),  # 16:30-17:00
]

for start, end in arthur_intervals:
    solver.add(z3.Or(S + 30 <= start, S >= end))

if solver.check() == z3.sat:
    model = solver.model()
    start_time = model[S].as_long()
    end_time = start_time + 30

    def to_hhmm(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"

    start_str = to_hhmm(start_time)
    end_str = to_hhmm(end_time)
    print(f"{start_str}:{end_str} Monday")
else:
    print("No solution found")