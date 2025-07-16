from z3 import *

def solve_scheduling():
    # Create the solver
    s = Solver()

    # Days: Monday=0, Tuesday=1, Wednesday=2, Thursday=3, Friday=4
    day = Int('day')
    start_time = Int('start_time')  # in minutes from 0:00

    # Constraints for day: must be 0 (Monday), 1 (Tuesday), or 4 (Friday) because Betty can't meet on Wednesday (2) or Thursday (3)
    s.add(Or(day == 0, day == 1, day == 4))

    # Meeting duration is 1 hour (60 minutes)
    duration = 60
    end_time = start_time + duration

    # Work hours are 9:00 to 17:00 (540 to 1020 minutes)
    s.add(start_time >= 540)
    s.add(end_time <= 1020)

    # Betty's busy times for each day
    betty_busy = {
        0: [(600, 630), (690, 750), (960, 990)],  # Monday 10:00-10:30, 11:30-12:30, 16:00-16:30
        1: [(570, 600), (630, 660), (720, 750), (810, 900), (990, 1020)],  # Tuesday 9:30-10:00, 10:30-11:00, 12:00-12:30, 13:30-15:00, 16:30-17:00
        4: [(540, 600), (690, 720), (750, 780), (870, 900)]  # Friday 9:00-10:00, 11:30-12:00, 12:30-13:00, 14:30-15:00
    }

    # Megan's busy times for each day
    megan_busy = {
        0: [(540, 1020)],  # Monday all day
        1: [(540, 570), (600, 630), (720, 840), (900, 930), (960, 990)],  # Tuesday 9:00-9:30, 10:00-10:30, 12:00-14:00, 15:00-15:30, 16:00-16:30
        2: [(570, 630), (660, 690), (750, 780), (810, 870), (930, 1020)],  # Wednesday 9:30-10:30, 11:00-11:30, 12:30-13:00, 13:30-14:30, 15:30-17:00
        3: [(540, 630), (690, 840), (870, 900), (930, 990)],  # Thursday 9:00-10:30, 11:30-14:00, 14:30-15:00, 15:30-16:30
        4: [(540, 1020)]  # Friday all day
    }

    # For the selected day, the meeting must not overlap with any busy slots for Betty and Megan
    def no_overlap(busy_slots, s_time, e_time):
        constraints = []
        for (busy_start, busy_end) in busy_slots:
            # The meeting does not overlap with this busy slot if it's entirely before or after
            constraints.append(Or(e_time <= busy_start, s_time >= busy_end))
        return And(constraints)

    # Constraints for Betty
    betty_constraints = []
    for d in betty_busy:
        betty_constraints.append(And(day == d, no_overlap(betty_busy[d], start_time, end_time)))
    s.add(Or(betty_constraints))

    # Constraints for Megan
    megan_constraints = []
    for d in megan_busy:
        megan_constraints.append(And(day == d, no_overlap(megan_busy[d], start_time, end_time)))
    s.add(Or(megan_constraints))

    # Check if a solution exists
    if s.check() == sat:
        model = s.model()
        d = model[day].as_long()
        st = model[start_time].as_long()
        et = st + duration

        # Convert day number to day name
        day_names = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']
        day_name = day_names[d]

        # Convert start and end times from minutes to HH:MM format
        def minutes_to_time(minutes):
            hh = minutes // 60
            mm = minutes % 60
            return f"{hh:02d}:{mm:02d}"

        start_str = minutes_to_time(st)
        end_str = minutes_to_time(et)

        print(f"SOLUTION:")
        print(f"Day: {day_name}")
        print(f"Start Time: {start_str}")
        print(f"End Time: {end_str}")
    else:
        print("No solution found")

solve_scheduling()