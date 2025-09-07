import z3

def minutes_to_time(minutes):
    hours = 9 + (minutes // 60)
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

solver = z3.Solver()

S = z3.Int('S')

# Work hours: 9:00 (0) to 17:00 (480)
solver.add(S >= 0)
solver.add(S + 30 <= 480)

# Frank's constraint: end time <= 9:30 (30 minutes)
solver.add(S + 30 <= 30)

# Emily's busy intervals
busy_emily = [
    (60, 90),   # 10:00-10:30
    (150, 210), # 11:30-12:30
    (300, 360), # 14:00-15:00
    (420, 450)  # 16:00-16:30
]

# Melissa's busy intervals
busy_melissa = [
    (30, 60),   # 9:30-10:00
    (330, 360)  # 14:30-15:00
]

# Frank's busy intervals
busy_frank = [
    (60, 90),       # 10:00-10:30
    (120, 150),     # 11:00-11:30
    (210, 240),     # 12:30-13:00
    (270, 330),     # 13:30-14:30
    (360, 420),     # 15:00-16:00
    (450, 480)      # 16:30-17:00
]

# Add constraints for non-overlapping with each participant's busy times
for b_start, b_end in busy_emily + busy_melissa + busy_frank:
    solver.add(z3.Or(S + 30 <= b_start, S >= b_end))

if solver.check() == z3.sat:
    model = solver.model()
    start_minutes = model[S].as_long()
    end_minutes = start_minutes + 30
    start_time = minutes_to_time(start_minutes)
    end_time = minutes_to_time(end_minutes)
    print(f"Monday {start_time}:{end_time}")
else:
    print("No solution found")