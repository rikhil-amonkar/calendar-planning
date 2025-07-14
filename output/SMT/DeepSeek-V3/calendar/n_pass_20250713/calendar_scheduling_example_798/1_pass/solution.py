from z3 import *

def solve_scheduling():
    # Define variables
    day = Int('day')  # 0: Monday, 1: Tuesday, 2: Wednesday
    start_time = Int('start_time')  # in minutes from 00:00
    end_time = Int('end_time')

    # Constraints for day: must be 0, 1, or 2
    constraints = [Or(day == 0, day == 1, day == 2)]

    # Constraints for time: between 9:00 (540) and 17:00 (1020)
    constraints.append(start_time >= 540)
    constraints.append(end_time <= 1020)
    constraints.append(end_time == start_time + 30)

    # Nancy's busy slots
    nancy_busy = [
        # Monday
        [(600, 630), (690, 750), (810, 840), (870, 930), (960, 1020)],
        # Tuesday
        [(570, 630), (660, 690), (720, 750), (780, 810), (930, 960)],
        # Wednesday
        [(600, 690), (810, 960)]
    ]

    # Jose's busy slots
    jose_busy = [
        # Monday: all day (9:00-17:00)
        [(540, 1020)],
        # Tuesday: all day (9:00-17:00)
        [(540, 1020)],
        # Wednesday
        [(540, 570), (600, 750), (810, 870), (900, 1020)]
    ]

    # Function to add constraints that the meeting does not overlap with any busy slot for a given day
    def add_no_overlap_constraints(day_var, start, end, busy_slots_per_day):
        for day_idx, slots in enumerate(busy_slots_per_day):
            for (busy_start, busy_end) in slots:
                constraints.append(Implies(day_var == day_idx, 
                              Or(end <= busy_start, start >= busy_end)))

    # Add constraints for Nancy and Jose
    add_no_overlap_constraints(day, start_time, end_time, nancy_busy)
    add_no_overlap_constraints(day, start_time, end_time, jose_busy)

    # Check for each day in order to find the earliest possible slot
    for d in [0, 1, 2]:
        s = Solver()
        for c in constraints:
            s.add(c)
        s.add(day == d)
        if s.check() == sat:
            model = s.model()
            st = model[start_time].as_long()
            et = model[end_time].as_long()
            day_name = ["Monday", "Tuesday", "Wednesday"][d]
            print(f"SOLUTION:")
            print(f"Day: {day_name}")
            print(f"Start Time: {st//60:02d}:{st%60:02d}")
            print(f"End Time: {et//60:02d}:{et%60:02d}")
            return

    print("No solution found")

solve_scheduling()