# Meeting scheduler using Z3 SMT solver
# Task: Schedule a 30-minute meeting for Andrew, Grace, and Samuel on Monday between 09:00 and 17:00.
# Constraints:
# - Andrew: free all day
# - Grace: free all day
# - Samuel blocks: 09:00-10:30, 11:30-12:00, 13:00-13:30, 14:00-16:00, 16:30-17:00
# Preference: earliest possible time

from z3 import Optimize, Int, Or, sat

def to_minutes(hh, mm):
    return hh * 60 + mm

def to_hhmm(total_minutes):
    h = total_minutes // 60
    m = total_minutes % 60
    return f"{h:02d}:{m:02d}"

def main():
    day = "Monday"
    work_start = to_minutes(9, 0)
    work_end = to_minutes(17, 0)
    duration = 30  # minutes

    # Participants' blocked intervals as [start_min, end_min) in minutes since midnight
    andrew_blocks = []  # free all day
    grace_blocks = []   # free all day
    samuel_blocks = [
        (to_minutes(9, 0),  to_minutes(10, 30)),
        (to_minutes(11, 30), to_minutes(12, 0)),
        (to_minutes(13, 0), to_minutes(13, 30)),
        (to_minutes(14, 0), to_minutes(16, 0)),
        (to_minutes(16, 30), to_minutes(17, 0)),
    ]

    all_blocks = {
        "Andrew": andrew_blocks,
        "Grace": grace_blocks,
        "Samuel": samuel_blocks,
    }

    opt = Optimize()
    start = Int("start")
    end = Int("end")

    # Meeting duration and within work hours
    opt.add(end == start + duration)
    opt.add(start >= work_start)
    opt.add(end <= work_end)

    # No overlap with any participant's blocked intervals
    for person, blocks in all_blocks.items():
        for (b_start, b_end) in blocks:
            # Either the meeting ends before the block starts, or it starts after the block ends
            opt.add(Or(end <= b_start, start >= b_end))

    # Preference: earliest possible start
    opt.minimize(start)

    if opt.check() != sat:
        raise RuntimeError("No feasible meeting time found, but the problem statement guarantees a solution.")

    model = opt.model()
    s = model[start].as_long()
    e = model[end].as_long()
    s_str = to_hhmm(s)
    e_str = to_hhmm(e)

    # Required outputs:
    # 1) Time in HH:MM:HH:MM
    print(f"{s_str}:{e_str}")
    # 2) Day of the week
    print(day)
    # 3) Include time range with braces as explicitly requested
    print(f"{{{s_str}:{e_str}}} {day}")

if __name__ == "__main__":
    main()