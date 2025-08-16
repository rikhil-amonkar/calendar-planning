import z3

solver = z3.Solver()

S = z3.Int('S')

# Work hours are from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration is 30 minutes, so S must be between 540 and 990 inclusive
solver.add(S >= 540)
solver.add(S <= 990)

# All blocked intervals for participants in (start, end) minutes format
blocked_intervals = [
    # Joe
    (570, 600), (630, 660),
    # Keith
    (690, 720), (900, 930),
    # Patricia
    (540, 570), (780, 810),
    # Nancy
    (540, 660), (690, 990),
    # Pamela
    (540, 600), (630, 660), (690, 750), (780, 840), (870, 900), (930, 960), (990, 1020)
]

# Add constraints to avoid overlap with blocked intervals
for start, end in blocked_intervals:
    solver.add(z3.Or(S + 30 <= start, S >= end))

if solver.check() == z3.sat:
    model = solver.model()
    s_val = model[S].as_long()
    start_time = s_val
    end_time = s_val + 30

    def to_time_str(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"

    print("SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {to_time_str(start_time)}")
    print(f"End Time: {to_time_str(end_time)}")
else:
    print("No solution found.")