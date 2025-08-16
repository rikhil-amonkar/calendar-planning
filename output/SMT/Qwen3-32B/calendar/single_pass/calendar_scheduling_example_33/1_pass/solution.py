import z3

solver = z3.Solver()

s = z3.Int('s')

# Work hours from 9:00 (540) to 17:00 (1020). The meeting is 30 min, so start can be up to 990 (16:30)
solver.add(s >= 540)
solver.add(s <= 990)

# Bobby's preference: meeting ends by 15:00 (900 min)
solver.add(s + 30 <= 900)  # s <= 870

# Define busy intervals for each person
busy_lisa = [
    (9*60, 10*60),           # 9:00-10:00
    (10*60+30, 11*60+30),    # 10:30-11:30
    (12*60+30, 13*60),       # 12:30-13:00
    (16*60, 16*60+30)        # 16:00-16:30
]

busy_bobby = [
    (9*60, 9*60 + 30),        # 9:00-9:30
    (10*60, 10*60 + 30),      # 10:00-10:30
    (11*60+30, 12*60),        # 11:30-12:00
    (15*60, 15*60 + 30)       # 15:00-15:30
]

busy_randy = [
    (9*60+30, 10*60),         # 9:30-10:00
    (10*60+30, 11*60),        # 10:30-11:00
    (11*60+30, 12*60+30),     # 11:30-12:30
    (13*60, 13*60+30),        # 13:00-13:30
    (14*60+30, 15*60+30),     # 14:30-15:30
    (16*60, 16*60+30)         # 16:00-16:30
]

# Add constraints for Lisa's busy times
for start, end in busy_lisa:
    solver.add(z3.Or(s >= end, s + 30 <= start))

# Add constraints for Bobby's busy times
for start, end in busy_bobby:
    solver.add(z3.Or(s >= end, s + 30 <= start))

# Add constraints for Randy's busy times
for start, end in busy_randy:
    solver.add(z3.Or(s >= end, s + 30 <= start))

if solver.check() == z3.sat:
    model = solver.model()
    start = model[s].as_long()
    end_time = start + 30
    # Convert to HH:MM format
    def to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"
    day = "Monday"
    print("SOLUTION:")
    print(f"Day: {day}")
    print(f"Start Time: {to_time(start)}")
    print(f"End Time: {to_time(end_time)}")
else:
    print("No solution found.")