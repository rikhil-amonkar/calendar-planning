from z3 import *

def schedule_meeting():
    solver = Solver()

    # Define variables
    day = Int('day')
    start = Int('start')
    end = start + 30

    # Global constraints
    solver.add(And(day >= 0, day <= 2))
    solver.add(And(start >= 540, start <= 990))
    solver.add(Or(day != 2, end <= 810))  # Ruth doesn't want to meet on Wednesday after 13:30

    # Define busy intervals for each participant per day
    nicole_busy = {
        0: [(540, 570), (780, 810), (870, 930)],
        1: [(540, 570), (690, 780), (870, 930)],
        2: [(600, 660), (750, 900), (960, 1020)]
    }

    ruth_busy = {
        0: [(540, 1020)],
        1: [(540, 1020)],
        2: [(540, 630), (660, 690), (720, 750), (810, 930), (960, 990)]
    }

    # Add constraints for each busy interval
    for busy_dict in [nicole_busy, ruth_busy]:
        for d in busy_dict:
            for a, b in busy_dict[d]:
                solver.add(Implies(day == d, Or(end <= a, start >= b)))

    # Check for solution
    if solver.check() == sat:
        m = solver.model()
        day_val = m[day].as_long()
        start_val = m[start].as_long()
        end_val = start_val + 30

        # Convert day to name
        days = ['Monday', 'Tuesday', 'Wednesday']
        day_name = days[day_val]

        # Convert minutes to HH:MM format
        def to_time_str(minutes):
            h = minutes // 60
            m = minutes % 60
            return f"{h:02d}:{m:02d}"

        start_str = to_time_str(start_val)
        end_str = to_time_str(end_val)

        # Output the solution
        print("SOLUTION:")
        print(f"Day: {day_name}")
        print(f"Start Time: {start_str}")
        print(f"End Time: {end_str}")
    else:
        print("No solution found.")

# Run the function
schedule_meeting()