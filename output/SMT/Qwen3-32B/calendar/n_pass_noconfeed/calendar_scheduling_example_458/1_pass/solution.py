import z3

solver = z3.Solver()

s = z3.Int('s')

# Overall time constraints: between 9:00 (0) and 16:30 (450)
solver.add(s >= 0)
solver.add(s <= 450)

# Wayne's preference: after 14:00 (300 minutes)
solver.add(s >= 300)

# All busy intervals
all_intervals = [
    # Melissa
    (60, 120),
    (210, 300),
    (360, 390),
    # Gregory
    (210, 240),
    (390, 420),
    # Victoria
    (0, 30),
    (90, 150),
    (240, 300),
    (330, 360),
    (390, 450),
    # Thomas
    (60, 180),
    (210, 240),
    (330, 420),
    # Jennifer
    (0, 30),
    (60, 90),
    (120, 240),
    (270, 330),
    (360, 390),
    (420, 450),
]

for start, end in all_intervals:
    solver.add(z3.Or(s + 30 <= start, s >= end))

if solver.check() == z3.sat:
    model = solver.model()
    s_val = model[s].as_long()
    # Convert to time
    def to_time(minutes):
        total = 9 * 60 + minutes
        h = total // 60
        m = total % 60
        return f"{h:02d}:{m:02d}"
    start_time = to_time(s_val)
    end_time = to_time(s_val + 30)
    print(f"{{{start_time}:{end_time}}} Monday")
else:
    print("No solution found")