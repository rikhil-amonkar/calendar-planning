from z3 import *

def solve_scheduling():
    # Create the solver
    s = Solver()

    # Define variables
    day = Int('day')  # 0 for Monday, 1 for Tuesday
    start_h = Int('start_h')
    start_m = Int('start_m')
    end_h = Int('end_h')
    end_m = Int('end_m')

    # Constraints for day
    s.add(Or(day == 0, day == 1))

    # Constraints for start and end times (30-minute meeting)
    s.add(start_h >= 9)
    s.add(start_h <= 16)  # Since meeting is 30 minutes, latest start is 16:30
    s.add(start_m >= 0)
    s.add(start_m < 60)
    s.add(end_h == start_h)
    s.add(end_m == start_m + 30)
    # Handle minute overflow (e.g., 10:30 + 30 minutes is 11:00)
    s.add(If(start_m + 30 >= 60,
             And(end_h == start_h + 1, end_m == (start_m + 30) % 60),
             And(end_h == start_h, end_m == start_m + 30)))
    s.add(end_h <= 17)
    s.add(If(end_h == 17, end_m == 0, True))  # End time cannot exceed 17:00

    # Bobby's busy intervals
    # Monday: 14:30-15:00
    bobby_monday = [
        (14, 30, 15, 0)
    ]
    # Tuesday: 9:00-11:30, 12:00-12:30, 13:00-15:00, 15:30-17:00
    bobby_tuesday = [
        (9, 0, 11, 30),
        (12, 0, 12, 30),
        (13, 0, 15, 0),
        (15, 30, 17, 0)
    ]

    # Michael's busy intervals
    # Monday: 9:00-10:00, 10:30-13:30, 14:00-15:00, 15:30-17:00
    michael_monday = [
        (9, 0, 10, 0),
        (10, 30, 13, 30),
        (14, 0, 15, 0),
        (15, 30, 17, 0)
    ]
    # Tuesday: 9:00-10:30, 11:00-11:30, 12:00-14:00, 15:00-16:00, 16:30-17:00
    michael_tuesday = [
        (9, 0, 10, 30),
        (11, 0, 11, 30),
        (12, 0, 14, 0),
        (15, 0, 16, 0),
        (16, 30, 17, 0)
    ]

    # Function to check if two intervals overlap
    def no_overlap(s_h, s_m, e_h, e_m, busy_s_h, busy_s_m, busy_e_h, busy_e_m):
        # Meeting starts before busy ends and ends after busy starts
        return Or(
            e_h < busy_s_h,
            And(e_h == busy_s_h, e_m <= busy_s_m),
            s_h > busy_e_h,
            And(s_h == busy_e_h, s_m >= busy_e_m)
        )

    # Constraints for Bobby's busy intervals
    for (bs_h, bs_m, be_h, be_m) in bobby_monday:
        s.add(If(day == 0,
                 no_overlap(start_h, start_m, end_h, end_m, bs_h, bs_m, be_h, be_m),
                 True))
    for (bs_h, bs_m, be_h, be_m) in bobby_tuesday:
        s.add(If(day == 1,
                 no_overlap(start_h, start_m, end_h, end_m, bs_h, bs_m, be_h, be_m),
                 True))

    # Constraints for Michael's busy intervals
    for (bs_h, bs_m, be_h, be_m) in michael_monday:
        s.add(If(day == 0,
                 no_overlap(start_h, start_m, end_h, end_m, bs_h, bs_m, be_h, be_m),
                 True))
    for (bs_h, bs_m, be_h, be_m) in michael_tuesday:
        s.add(If(day == 1,
                 no_overlap(start_h, start_m, end_h, end_m, bs_h, bs_m, be_h, be_m),
                 True))

    # Find the earliest possible time by minimizing (day, start_h, start_m)
    # We'll use a lexicographic order: day first, then start_h, then start_m
    opt = Optimize()
    opt.add(s.assertions())
    opt.minimize(day * 10000 + start_h * 100 + start_m)

    if opt.check() == sat:
        model = opt.model()
        d = model[day].as_long()
        sh = model[start_h].as_long()
        sm = model[start_m].as_long()
        eh = model[end_h].as_long()
        em = model[end_m].as_long()

        day_str = "Monday" if d == 0 else "Tuesday"
        start_time = f"{sh:02d}:{sm:02d}"
        end_time = f"{eh:02d}:{em:02d}"
        print("SOLUTION:")
        print(f"Day: {day_str}")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

solve_scheduling()