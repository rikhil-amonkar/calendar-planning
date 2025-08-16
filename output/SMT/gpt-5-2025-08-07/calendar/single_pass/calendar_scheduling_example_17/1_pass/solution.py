from z3 import Optimize, Int, Or

def to_minutes(h, m):
    return h * 60 + m

def fmt_time(total_minutes):
    h = total_minutes // 60
    m = total_minutes % 60
    return f"{h:02d}:{m:02d}"

def main():
    # Constants
    day = "Monday"
    duration = 30  # minutes
    work_start = to_minutes(9, 0)   # 09:00
    work_end = to_minutes(17, 0)    # 17:00

    # Busy schedules (start, end) in minutes from 00:00
    margaret_busy = [
        (to_minutes(9, 0),  to_minutes(10, 0)),
        (to_minutes(10, 30), to_minutes(11, 0)),
        (to_minutes(11, 30), to_minutes(12, 0)),
        (to_minutes(13, 0), to_minutes(13, 30)),
        (to_minutes(15, 0), to_minutes(15, 30)),
    ]

    donna_busy = [
        (to_minutes(14, 30), to_minutes(15, 0)),
        (to_minutes(16, 0), to_minutes(16, 30)),
    ]

    helen_busy = [
        (to_minutes(9, 0),  to_minutes(9, 30)),
        (to_minutes(10, 0), to_minutes(11, 30)),
        (to_minutes(13, 0), to_minutes(14, 0)),
        (to_minutes(14, 30), to_minutes(15, 0)),
        (to_minutes(15, 30), to_minutes(17, 0)),
    ]

    # Preference: Helen does not want to meet on Monday after 13:30
    helen_latest_end = to_minutes(13, 30)

    # Z3 optimize solver (to find the earliest feasible time)
    opt = Optimize()
    start = Int("start")
    end = start + duration

    # Work hours constraint
    opt.add(start >= work_start)
    opt.add(end <= work_end)

    # Helen's preference constraint
    opt.add(end <= helen_latest_end)

    # Non-overlap constraints for each participant
    def add_non_overlap(intervals):
        for s, e in intervals:
            opt.add(Or(end <= s, start >= e))

    add_non_overlap(margaret_busy)
    add_non_overlap(donna_busy)
    add_non_overlap(helen_busy)

    # Minimize start time to get the earliest feasible meeting
    opt.minimize(start)

    if opt.check() == sat:
        model = opt.model()
        start_min = model.evaluate(start).as_long()
        end_min = start_min + duration

        print("SOLUTION:")
        print(f"Day: {day}")
        print(f"Start Time: {fmt_time(start_min)}")
        print(f"End Time: {fmt_time(end_min)}")
    else:
        # As per the problem statement, a solution exists. This branch should not trigger.
        print("SOLUTION:")
        print(f"Day: {day}")
        print("Start Time: 00:00")
        print("End Time: 00:00")

if __name__ == "__main__":
    main()