from z3 import *

def minutes_to_hhmm(m):
    h = m // 60
    mi = m % 60
    return f"{h:02d}:{mi:02d}"

def schedule_meeting():
    # Work hours (Monday): 09:00 to 17:00
    WORK_START = 9 * 60   # 540
    WORK_END   = 17 * 60  # 1020

    duration = 30  # minutes

    # Busy intervals in minutes from midnight [start, end)
    # Eric's schedule (Monday)
    eric_busy = [
        (12*60, 13*60),
        (14*60, 15*60),
    ]

    # Henry's schedule (Monday)
    henry_busy = [
        (9*60 + 30, 10*60),     # 09:30 - 10:00
        (10*60 + 30, 11*60),    # 10:30 - 11:00
        (11*60 + 30, 12*60 + 30), # 11:30 - 12:30
        (13*60, 13*60 + 30),    # 13:00 - 13:30
        (14*60 + 30, 15*60),    # 14:30 - 15:00
        (16*60, 17*60),         # 16:00 - 17:00
    ]

    # Z3 variables
    start = Int('start')
    end = Int('end')

    opt = Optimize()

    # Duration and work hours constraints
    opt.add(start >= WORK_START)
    opt.add(end == start + duration)
    opt.add(end <= WORK_END)

    # No-overlap constraints for each participant: for each busy [b_start, b_end),
    # enforce (end <= b_start) OR (start >= b_end)
    def add_no_overlap(intervals):
        for bs, be in intervals:
            opt.add(Or(end <= bs, start >= be))

    add_no_overlap(eric_busy)
    add_no_overlap(henry_busy)

    # Preference: Henry would rather not meet after 10:00.
    # Encourage start <= 10:00 with a soft constraint.
    ten_am = 10 * 60
    opt.add_soft(start <= ten_am, weight='1')

    # Tie-breaker: choose the earliest valid time
    opt.minimize(start)

    if opt.check() != sat:
        raise RuntimeError("No solution found (but the prompt guarantees one exists).")

    model = opt.model()
    s = model[start].as_long()
    e = model[end].as_long()

    day = "Monday"
    start_str = minutes_to_hhmm(s)
    end_str = minutes_to_hhmm(e)

    print("SOLUTION:")
    print(f"Day: {day}")
    print(f"Start Time: {start_str} (24-hour format)")
    print(f"End Time: {end_str} (24-hour format)")

if __name__ == "__main__":
    schedule_meeting()