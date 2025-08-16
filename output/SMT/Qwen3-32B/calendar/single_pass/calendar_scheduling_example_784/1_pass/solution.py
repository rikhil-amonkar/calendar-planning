from z3 import *

# Initialize solver
solver = Solver()

# Define variables
day = Int('day')
start = Int('start')
end = start + 60

# Constraints for day and start time
solver.add(Or(day == 0, day == 1, day == 2))  # 0: Monday, 1: Tuesday, 2: Wednesday
solver.add(And(start >= 540, start <= 960))  # 9:00 to 16:00 (since 1h meeting)

# Blocked intervals for each participant
judith_blocked = {
    0: [(720, 750)],  # Monday 12:00-12:30
    2: [(690, 720)],  # Wednesday 11:30-12:00
}

timothy_blocked = {
    0: [(570, 600), (630, 690), (750, 840), (930, 1020)],  # Monday
    1: [(570, 780), (810, 840), (870, 1020)],  # Tuesday
    2: [(540, 570), (630, 660), (810, 870), (900, 930), (960, 990)],  # Wednesday
}

# Add constraints for Judith's blocked intervals
for d in judith_blocked:
    for b_start, b_end in judith_blocked[d]:
        solver.add(Implies(day == d, Or(start + 60 <= b_start, b_end <= start)))

# Add constraints for Timothy's blocked intervals
for d in timothy_blocked:
    for b_start, b_end in timothy_blocked[d]:
        solver.add(Implies(day == d, Or(start + 60 <= b_start, b_end <= start)))

# Check for solution
if solver.check() == sat:
    model = solver.model()
    day_val = model[day].as_long()
    start_val = model[start].as_long()
    end_val = start_val + 60

    days = ['Monday', 'Tuesday', 'Wednesday']
    day_str = days[day_val]

    def to_time_str(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"

    print("SOLUTION:")
    print(f"Day: {day_str}")
    print(f"Start Time: {to_time_str(start_val)}")
    print(f"End Time: {to_time_str(end_val)}")
else:
    print("No solution found")