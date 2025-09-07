from z3 import *

def main():
    solver = Optimize()  # Use Optimize instead of Solver

    day = Int('day')
    start_time = Int('start_time')

    # Basic constraints
    solver.add(0 <= day, day <= 4)
    solver.add(540 <= start_time, start_time <= 990)

    # Daniel's day preferences: not Wednesday (2) or Thursday (3)
    solver.add(And(day != 2, day != 3))

    # Bradley's day preferences: not Monday (0), Friday (4)
    solver.add(And(day != 0, day != 4))

    # Bradley's Tuesday before 12:00 (720) constraint
    solver.add(Implies(day == 1, start_time >= 720))

    # Define busy intervals for Daniel and Bradley
    daniel_busy = [
        # Monday (0)
        [(570, 630), (720, 750), (780, 840), (870, 900), (930, 960)],
        # Tuesday (1)
        [(660, 720), (780, 810), (930, 960), (990, 1020)],
        # Wednesday (2)
        [(540, 600), (840, 870)],
        # Thursday (3)
        [(630, 660), (720, 780), (870, 900), (930, 960)],
        # Friday (4)
        [(540, 570), (690, 720), (780, 810), (990, 1020)]
    ]

    bradley_busy = [
        # Monday (0)
        [(570, 660), (690, 720), (750, 780), (840, 900)],
        # Tuesday (1)
        [(630, 660), (720, 780), (810, 840), (930, 990)],
        # Wednesday (2)
        [(540, 600), (660, 780), (810, 840), (870, 1020)],
        # Thursday (3)
        [(540, 750), (810, 840), (870, 900), (930, 990)],
        # Friday (4)
        [(540, 570), (600, 750), (780, 810), (840, 870), (930, 990)]
    ]

    # Add Daniel's busy time constraints
    for d in range(5):
        busy_intervals = daniel_busy[d]
        if not busy_intervals:
            continue
        constraints = []
        for (bs, be) in busy_intervals:
            constraints.append(Or(start_time + 30 <= bs, be <= start_time))
        day_constraints = And(constraints)
        solver.add(Implies(day == d, day_constraints))

    # Add Bradley's busy time constraints
    for d in range(5):
        busy_intervals = bradley_busy[d]
        if not busy_intervals:
            continue
        constraints = []
        for (bs, be) in busy_intervals:
            constraints.append(Or(start_time + 30 <= bs, be <= start_time))
        day_constraints = And(constraints)
        solver.add(Implies(day == d, day_constraints))

    # Add objective to minimize start_time
    solver.minimize(start_time)

    if solver.check() == sat:
        model = solver.model()
        day_val = model[day].as_long()
        start_val = model[start_time].as_long()
        end_val = start_val + 30
        days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
        day_name = days[day_val]

        def to_time(mins):
            hours = mins // 60
            minutes = mins % 60
            return f"{hours:02d}:{minutes:02d}"

        start_time_str = to_time(start_val)
        end_time_str = to_time(end_val)
        time_range = f"{start_time_str}:{end_time_str}"
        print(f"{time_range} {day_name}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()