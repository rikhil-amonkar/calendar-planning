import z3

# Define the busy intervals for each day (0=Mon, 1=Tue, 2=Wed, 3=Thu)
betty_busy = [
    # Monday
    [(600, 630), (810, 840), (900, 930), (960, 990)],
    # Tuesday
    [(540, 570), (690, 720), (750, 780), (810, 840), (990, 1020)],
    # Wednesday
    [(570, 630), (780, 810), (840, 870)],
    # Thursday
    [(570, 600), (690, 720), (840, 870), (900, 930), (990, 1020)],
]

scott_busy = [
    # Monday
    [(570, 900), (930, 960), (990, 1020)],
    # Tuesday
    [(540, 570), (600, 660), (690, 720), (750, 810), (840, 900), (960, 990)],
    # Wednesday
    [(570, 750), (780, 810), (840, 870), (900, 930), (960, 990)],
    # Thursday
    [(540, 570), (600, 630), (660, 720), (750, 780), (900, 960), (990, 1020)],
]

solver = z3.Solver()

day = z3.Int('day')
start = z3.Int('start')

# Constraints for Betty's day restrictions
solver.add(z3.And(day >= 1, day <= 3))  # day can't be Monday (0)
solver.add(start >= 540, start <= 990)  # start between 9:00 and 16:30 (since 17:00 - 30 min)

# Betty's additional constraints on Tuesday and Thursday
solver.add(z3.Or(day != 1, start >= 900))  # Tuesday (day 1) requires start >= 15:00 (900)
solver.add(z3.Or(day != 3, start >= 900))  # Thursday (day 3) requires start >= 15:00

# Add constraints for Betty's busy times
for d in range(4):
    for (s, e) in betty_busy[d]:
        solver.add(z3.Or(day != d, start >= e, start + 30 <= s))

# Add constraints for Scott's busy times
for d in range(4):
    for (s, e) in scott_busy[d]:
        solver.add(z3.Or(day != d, start >= e, start + 30 <= s))

if solver.check() == z3.sat:
    model = solver.model()
    day_val = model[day].as_long()
    start_val = model[start].as_long()
    end_val = start_val + 30

    # Convert to day name
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']
    day_name = days[day_val]

    # Convert start and end to HH:MM
    def to_time(m):
        h = m // 60
        m_remain = m % 60
        return f"{h:02d}:{m_remain:02d}"

    print("SOLUTION:")
    print(f"Day: {day_name}")
    print(f"Start Time: {to_time(start_val)}")
    print(f"End Time: {to_time(end_val)}")
else:
    print("No solution found.")