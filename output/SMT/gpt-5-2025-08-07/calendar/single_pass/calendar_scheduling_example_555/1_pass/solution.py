from z3 import *

def to_minutes(hh_mm):
    h, m = map(int, hh_mm.split(":"))
    return h * 60 + m

def from_minutes(m):
    h = m // 60
    mins = m % 60
    return f"{h:02d}:{mins:02d}"

def schedule_meeting():
    # Problem data
    day = "Monday"
    work_start = to_minutes("09:00")
    work_end = to_minutes("17:00")
    duration = 30  # minutes

    # Existing schedules (busy intervals) for participants on Monday
    # Evelyn: no meetings -> no busy intervals
    # Randy busy: [9:00-10:30], [11:00-15:30], [16:00-17:00]
    randy_busy = [
        (to_minutes("09:00"), to_minutes("10:30")),
        (to_minutes("11:00"), to_minutes("15:30")),
        (to_minutes("16:00"), to_minutes("17:00")),
    ]

    # Preferences/constraints
    # Evelyn does not want to meet after 13:00 (meeting must end by 13:00)
    evelyn_end_by = to_minutes("13:00")

    # Z3 variables
    start = Int("start")
    end = Int("end")

    s = Optimize()

    # Core constraints
    s.add(end == start + duration)
    s.add(work_start <= start)
    s.add(end <= work_end)

    # Optional: align to 30-minute grid
    s.add(start % 30 == 0)

    # Evelyn preference: meeting must end by 13:00
    s.add(end <= evelyn_end_by)

    # Randy busy-time non-overlap constraints
    for (b_start, b_end) in randy_busy:
        # Meeting either ends before busy slot starts OR starts after busy slot ends
        s.add(Or(end <= b_start, start >= b_end))

    # Find the earliest feasible start time
    s.minimize(start)

    if s.check() == sat:
        m = s.model()
        start_time = m[start].as_long()
        end_time = m[end].as_long()
        print("SOLUTION:")
        print(f"Day: {day}")
        print(f"Start Time: {from_minutes(start_time)} (24-hour format)")
        print(f"End Time: {from_minutes(end_time)} (24-hour format)")
    else:
        # Problem statement guarantees a solution; this is a fallback.
        print("No feasible solution found.")

if __name__ == "__main__":
    schedule_meeting()