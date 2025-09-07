import z3

solver = z3.Solver()

start_time = z3.Int('start_time')
end_time = start_time + 30

# Work hours constraints (9:00 AM to 5:00 PM)
solver.add(start_time >= 540)  # 9:00 AM in minutes
solver.add(end_time <= 1020)   # 5:00 PM in minutes

# Melissa's preference: meeting must start by 14:00 (840 minutes)
solver.add(start_time <= 840)

# Function to add non-overlapping constraints for busy intervals
def add_constraints(participant_intervals):
    for busy_start, busy_end in participant_intervals:
        solver.add(z3.Or(start_time + 30 <= busy_start, start_time >= busy_end))

# Jeffrey's busy intervals (minutes)
jeffrey_intervals = [(570, 600), (630, 660)]  # 9:30-10:00, 10:30-11:00
add_constraints(jeffrey_intervals)

# Virginia's busy intervals
virginia_intervals = [(540, 570), (600, 630), (870, 900), (960, 990)]  # 9:00-9:30, 10:00-10:30, 14:30-15:00, 16:00-16:30
add_constraints(virginia_intervals)

# Melissa's busy intervals
melissa_intervals = [(540, 690), (720, 750), (780, 900), (960, 1020)]  # 9:00-11:30, 12:00-12:30, 13:00-15:00, 16:00-17:00
add_constraints(melissa_intervals)

if solver.check() == z3.sat:
    model = solver.model()
    start = model[start_time].as_long()
    end = start + 30

    def to_time(mins):
        hours = mins // 60
        minutes = mins % 60
        return f"{hours:02d}:{minutes:02d}"

    start_str = to_time(start)
    end_str = to_time(end)
    print(f"Monday {start_str}:{end_str}")
else:
    print("No solution found.")