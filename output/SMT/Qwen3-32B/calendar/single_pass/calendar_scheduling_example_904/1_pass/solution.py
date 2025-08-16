from z3 import *

# Define busy times for Daniel and Bradley
daniel_busy = [
    # Monday
    [(570, 630), (720, 750), (780, 840), (870, 900), (930, 960)],
    # Tuesday
    [(660, 720), (780, 810), (930, 960), (990, 1020)],
    # Wednesday
    [(540, 600), (840, 870)],
    # Thursday
    [(630, 660), (720, 780), (870, 900), (930, 960)],
    # Friday
    [(540, 570), (690, 720), (780, 810), (990, 1020)],
]

bradley_busy = [
    # Monday
    [(570, 660), (690, 720), (750, 780), (840, 900)],
    # Tuesday
    [(630, 660), (720, 780), (810, 840), (930, 990)],
    # Wednesday
    [(540, 600), (660, 780), (810, 840), (870, 1050)],
    # Thursday
    [(540, 750), (810, 840), (870, 900), (930, 990)],
    # Friday
    [(540, 570), (600, 750), (780, 810), (840, 870), (930, 990)],
]

def add_busy_constraints(participant_busy, solver, day_var, start_time_var):
    for d in range(5):
        intervals = participant_busy[d]
        constraints = []
        for a, b in intervals:
            constraints.append(Or(start_time_var + 30 <= a, start_time_var >= b))
        solver.add(Implies(day_var == d, And(*constraints)))

s = Solver()

day = Int('day')
start_time = Int('start_time')

# Basic constraints
s.add(And(0 <= day, day <= 4))
s.add(And(540 <= start_time, start_time <= 990))  # 9:00 to 16:30

# Daniel's preferences: not Wednesday (2) or Thursday (3)
s.add(And(day != 2, day != 3))

# Bradley's preferences: not Monday (0), not Friday (4), and on Tuesday (1) not before 12:00 (720)
s.add(And(day != 0, day != 4))
s.add(Or(day != 1, start_time >= 720))

# Add busy time constraints
add_busy_constraints(daniel_busy, s, day, start_time)
add_busy_constraints(bradley_busy, s, day, start_time)

if s.check() == sat:
    m = s.model()
    day_val = m[day].as_long()
    start_val = m[start_time].as_long()
    end_val = start_val + 30
    days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    day_name = days[day_val]
    start_h = start_val // 60
    start_m = start_val % 60
    end_h = end_val // 60
    end_m = end_val % 60
    start_time_str = f"{start_h:02d}:{start_m:02d}"
    end_time_str = f"{end_h:02d}:{end_m:02d}"
    print("SOLUTION:")
    print(f"Day: {day_name}")
    print(f"Start Time: {start_time_str}")
    print(f"End Time: {end_time_str}")
else:
    print("No solution found.")