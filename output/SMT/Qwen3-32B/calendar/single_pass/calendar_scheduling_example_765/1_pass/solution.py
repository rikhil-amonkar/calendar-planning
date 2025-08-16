from z3 import *

# Define the busy intervals for each participant and day
joshua_busy = {
    0: [(900, 930)],  # Monday
    1: [(690, 720), (780, 810), (870, 900)],  # Tuesday
    2: []  # Wednesday
}

joyce_busy = {
    0: [(540, 570), (600, 660), (690, 750), (780, 900), (930, 1020)],  # Monday
    1: [(540, 1020)],  # Tuesday
    2: [(540, 570), (600, 660), (750, 930), (960, 990)]  # Wednesday
}

# Initialize Z3 solver
solver = Solver()

# Define variables
day = Int('day')
start = Int('start')

# Add constraints for day and start time
solver.add(And(day >= 0, day <= 2))  # day is 0 (Monday), 1 (Tuesday), or 2 (Wednesday)
solver.add(And(start >= 540, start <= 990))  # start time between 9:00 (540) and 16:30 (990)
solver.add(Implies(day == 0, start >= 720))  # Joyce's preference for Monday

# Add constraints for Joshua's busy intervals
for day_num in joshua_busy:
    for (b_start, b_end) in joshua_busy[day_num]:
        cond = day == day_num
        not_overlap = Or(start + 30 <= b_start, start >= b_end)
        solver.add(Implies(cond, not_overlap))

# Add constraints for Joyce's busy intervals
for day_num in joyce_busy:
    for (b_start, b_end) in joyce_busy[day_num]:
        cond = day == day_num
        not_overlap = Or(start + 30 <= b_start, start >= b_end)
        solver.add(Implies(cond, not_overlap))

# Check for a solution
if solver.check() == sat:
    model = solver.model()
    day_val = model[day].as_long()
    start_val = model[start].as_long()
    end_val = start_val + 30

    # Convert day number to name
    days = ['Monday', 'Tuesday', 'Wednesday']
    day_name = days[day_val]

    # Convert minutes to HH:MM format
    def to_time(minutes):
        h = minutes // 60
        m = minutes % 60
        return f"{h:02d}:{m:02d}"

    start_time = to_time(start_val)
    end_time = to_time(end_val)

    print("SOLUTION:")
    print(f"Day: {day_name}")
    print(f"Start Time: {start_time}")
    print(f"End Time: {end_time}")
else:
    print("No solution found.")