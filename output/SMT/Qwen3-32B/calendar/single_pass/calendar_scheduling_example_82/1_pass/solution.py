import z3

solver = z3.Solver()

start = z3.Int('start')

solver.add(start >= 540)
solver.add(start <= 990)

all_intervals = [
    (570, 630), (900, 930), (960, 990),  # Michael's intervals
    (540, 720), (780, 900), (930, 960), (990, 1020)  # Arthur's intervals
]

for s, e in all_intervals:
    solver.add(z3.Or(start + 30 <= s, start >= e))

if solver.check() == z3.sat:
    model = solver.model()
    start_val = model[start].as_long()
    end_val = start_val + 30

    def to_time(minutes):
        h = minutes // 60
        m = minutes % 60
        return f"{h:02d}:{m:02d}"

    print("SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {to_time(start_val)}")
    print(f"End Time: {to_time(end_val)}")