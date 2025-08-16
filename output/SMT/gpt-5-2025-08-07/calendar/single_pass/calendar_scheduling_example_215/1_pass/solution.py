# Requires: z3-solver
# pip install z3-solver

from z3 import Optimize, Int, Or

def time_to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    return f"{m // 60:02d}:{m % 60:02d}"

def add_no_overlap_constraints(opt, start_var, duration, busy_intervals):
    for (s, e) in busy_intervals:
        # No overlap with [s, e): either meeting ends before s, or starts at/after e
        opt.add(Or(start_var + duration <= s, start_var >= e))

def main():
    # Problem data
    day = "Monday"
    work_start = time_to_minutes("09:00")
    work_end = time_to_minutes("17:00")
    duration = 30  # minutes

    # Busy intervals per participant on Monday (half-open [start, end))
    busy = {
        "Steven": [],  # free all day
        "Roy": [],     # free all day
        "Cynthia": [
            (time_to_minutes("09:30"), time_to_minutes("10:30")),
            (time_to_minutes("11:30"), time_to_minutes("12:00")),
            (time_to_minutes("13:00"), time_to_minutes("13:30")),
            (time_to_minutes("15:00"), time_to_minutes("16:00")),
        ],
        "Lauren": [
            (time_to_minutes("09:00"), time_to_minutes("09:30")),
            (time_to_minutes("10:30"), time_to_minutes("11:00")),
            (time_to_minutes("11:30"), time_to_minutes("12:00")),
            (time_to_minutes("13:00"), time_to_minutes("13:30")),
            (time_to_minutes("14:00"), time_to_minutes("14:30")),
            (time_to_minutes("15:00"), time_to_minutes("15:30")),
            (time_to_minutes("16:00"), time_to_minutes("17:00")),
        ],
        "Robert": [
            (time_to_minutes("10:30"), time_to_minutes("11:00")),
            (time_to_minutes("11:30"), time_to_minutes("12:00")),
            (time_to_minutes("12:30"), time_to_minutes("13:30")),
            (time_to_minutes("14:00"), time_to_minutes("16:00")),
        ],
    }

    # Z3 model
    start = Int("start")
    opt = Optimize()
    # Meeting must be within work hours
    opt.add(start >= work_start)
    opt.add(start + duration <= work_end)

    # No-overlap constraints for all participants
    for person, intervals in busy.items():
        add_no_overlap_constraints(opt, start, duration, intervals)

    # Preference: earliest start time
    opt.minimize(start)

    if opt.check() != 1:  # 1 == sat
        raise RuntimeError("No feasible schedule found, but a solution was expected.")

    model = opt.model()
    start_min = model[start].as_long()
    end_min = start_min + duration

    # Output in required format
    print("SOLUTION:")
    print(f"Day: {day}")
    print(f"Start Time: {minutes_to_time(start_min)}")
    print(f"End Time: {minutes_to_time(end_min)}")

if __name__ == "__main__":
    main()