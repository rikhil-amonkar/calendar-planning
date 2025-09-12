from z3 import *

# Define variables
day = Int('day')
start_time = Int('start_time')

solver = Solver()

# Day must be 0 (Monday), 1 (Tuesday), or 2 (Wednesday)
solver.add(And(day >= 0, day <= 2))

# Start time must be between 0 and 420 (inclusive)
solver.add(And(start_time >= 0, start_time <= 420))

# Judith's preference: avoid Monday
solver.add(day != 0)

# Judith's preference: if Wednesday, start after 12:00 (180 minutes)
solver.add(If(day == 2, start_time >= 180, True))

# Define blocked intervals for each day

# Tuesday: Timothy's blocked intervals
blocked_tuesday_timothy = [
    (30, 240),  # 9:30-13:00
    (270, 300), # 13:30-14:00
    (330, 480)  # 14:30-17:00
]

for bs, be in blocked_tuesday_timothy:
    solver.add(Implies(day == 1, Or(start_time + 60 <= bs, start_time >= be)))

# Wednesday: Judith's blocked interval
solver.add(Implies(day == 2, Or(start_time + 60 <= 150, start_time >= 180)))

# Wednesday: Timothy's blocked intervals
wed_blocked_timothy = [
    (0, 30),        # 9:00-9:30
    (90, 120),      # 10:30-11:00
    (270, 330),     # 13:30-14:30
    (360, 390),     # 15:00-15:30
    (420, 450)      # 16:00-16:30
]

for bs, be in wed_blocked_timothy:
    solver.add(Implies(day == 2, Or(start_time + 60 <= bs, start_time >= be)))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    day_val = model[day].as_long()
    start_val = model[start_time].as_long()
    end_val = start_val + 60

    # Convert minutes to hours and minutes
    def to_time(minutes):
        hours = 9 + minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"

    start_time_str = to_time(start_val)
    end_time_str = to_time(end_val)

    days = ["Monday", "Tuesday", "Wednesday"]
    day_name = days[day_val]

    print(f"{start_time_str}:{end_time_str} {day_name}")
else:
    print("No solution found.")