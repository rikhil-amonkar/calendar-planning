from z3 import *

def solve_scheduling():
    # Create the solver
    s = Solver()

    # Days: Monday=0, Tuesday=1, Wednesday=2, Thursday=3, Friday=4
    day = Int('day')
    start_time = Int('start_time')  # in minutes since 00:00

    # Meeting duration is 30 minutes
    duration = 30
    end_time = start_time + duration

    # Constraints for day: must be between 0 (Monday) and 4 (Friday)
    s.add(day >= 0, day <= 4)

    # Work hours are 9:00 (540) to 17:00 (1020)
    s.add(start_time >= 540)
    s.add(end_time <= 1020)

    # Eugene's busy times per day
    eugene_busy = {
        0: [(660, 720), (810, 840), (870, 900), (960, 990)],  # Monday 11:00-12:00, etc.
        2: [(540, 570), (660, 690), (720, 750), (810, 900)],  # Wednesday
        3: [(570, 600), (660, 750)],  # Thursday
        4: [(630, 660), (720, 750), (780, 810)]  # Friday
    }

    # Eric's busy times per day
    eric_busy = {
        0: [(540, 1020)],  # Monday all day
        1: [(540, 1020)],  # Tuesday all day
        2: [(540, 690), (720, 840), (870, 990)],  # Wednesday
        3: [(540, 1020)],  # Thursday all day
        4: [(540, 660), (690, 1020)]  # Friday
    }

    # Function to add constraints that the meeting does not overlap with any busy slots for a person on the selected day
    def add_no_overlap_constraints(busy_slots_dict, person_day):
        constraints = []
        for d in busy_slots_dict:
            slots = busy_slots_dict[d]
            for (busy_start, busy_end) in slots:
                # If the current day is d, then the meeting must not overlap with any busy slot
                constraint = Not(And(day == d,
                                    Or(
                                        And(start_time >= busy_start, start_time < busy_end),
                                        And(end_time > busy_start, end_time <= busy_end),
                                        And(start_time <= busy_start, end_time >= busy_end)
                                    )))
                constraints.append(constraint)
        return constraints

    # Add no-overlap constraints for Eugene and Eric
    s.add(add_no_overlap_constraints(eugene_busy, day))
    s.add(add_no_overlap_constraints(eric_busy, day))

    # Eric prefers to avoid Wednesday, so try other days first by adding a soft constraint
    # We first try to find a solution where day is not Wednesday (2)
    # If that's not possible, we relax the constraint
    temp_solver = Solver()
    temp_solver.add(s.assertions())
    temp_solver.add(day != 2)
    if temp_solver.check() == sat:
        s.add(day != 2)
    # else, proceed without this constraint

    # Check for a solution
    if s.check() == sat:
        m = s.model()
        day_val = m[day].as_long()
        start_val = m[start_time].as_long()
        end_val = start_val + duration

        # Convert day_val to day name
        days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
        day_name = days[day_val]

        # Convert start and end times to HH:MM format
        def minutes_to_time(minutes):
            h = minutes // 60
            m = minutes % 60
            return f"{h:02d}:{m:02d}"

        start_str = minutes_to_time(start_val)
        end_str = minutes_to_time(end_val)

        print(f"SOLUTION:")
        print(f"Day: {day_name}")
        print(f"Start Time: {start_str}")
        print(f"End Time: {end_str}")
    else:
        print("No solution found")

solve_scheduling()