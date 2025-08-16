from z3 import Int, Or, And, Optimize, sat

def minutes(h, m):
    return h * 60 + m

def format_time(total_minutes):
    h = total_minutes // 60
    m = total_minutes % 60
    return f"{h:02d}:{m:02d}"

def no_overlap(start, end, intervals):
    return And(*[Or(end <= s, start >= e) for (s, e) in intervals])

def main():
    # Work hours and meeting duration
    work_start = minutes(9, 0)
    work_end = minutes(17, 0)
    duration = 30

    # Participants' busy intervals on Monday (in minutes from 00:00)
    michael_busy = [
        (minutes(9, 30), minutes(10, 30)),
        (minutes(15, 0), minutes(15, 30)),
        (minutes(16, 0), minutes(16, 30)),
    ]
    eric_busy = []  # wide open
    arthur_busy = [
        (minutes(9, 0), minutes(12, 0)),
        (minutes(13, 0), minutes(15, 0)),
        (minutes(15, 30), minutes(16, 0)),
        (minutes(16, 30), minutes(17, 0)),
    ]

    # Z3 variables
    start = Int("start")
    end = Int("end")

    opt = Optimize()

    # Basic constraints
    opt.add(end == start + duration)
    opt.add(start >= work_start, end <= work_end)

    # Non-overlap constraints for each participant
    opt.add(no_overlap(start, end, michael_busy))
    opt.add(no_overlap(start, end, eric_busy))
    opt.add(no_overlap(start, end, arthur_busy))

    # Prefer the earliest feasible time
    opt.minimize(start)

    if opt.check() == sat:
        model = opt.model()
        s_val = model.eval(start).as_long()
        e_val = model.eval(end).as_long()
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {format_time(s_val)} (24-hour format)")
        print(f"End Time: {format_time(e_val)} (24-hour format)")
    else:
        # As per prompt, a solution exists, but handle just in case
        print("SOLUTION:")
        print("Day: Monday")
        print("Start Time: 00:00 (24-hour format)")
        print("End Time: 00:00 (24-hour format)")

if __name__ == "__main__":
    main()