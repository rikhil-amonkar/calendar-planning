# Requires: z3-solver
# pip install z3-solver

from z3 import *

# Days mapping
DAYS = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
MON, TUE, WED, THU, FRI = 0, 1, 2, 3, 4

def hm(h, m):
    return h * 60 + m

WORK_START = hm(9, 0)
WORK_END = hm(17, 0)
MEETING_DURATION = 60  # minutes

# Busy schedules per participant per day (times in minutes from 00:00, half-open intervals [start, end))
betty_busy = {
    MON: [(hm(10, 0), hm(10, 30)),
          (hm(11, 30), hm(12, 30)),
          (hm(16, 0), hm(16, 30))],
    TUE: [(hm(9, 30), hm(10, 0)),
          (hm(10, 30), hm(11, 0)),
          (hm(12, 0), hm(12, 30)),
          (hm(13, 30), hm(15, 0)),
          (hm(16, 30), hm(17, 0))],
    WED: [(hm(13, 30), hm(14, 0)),
          (hm(14, 30), hm(15, 0))],
    THU: [],  # No explicit blocks, but Betty cannot meet on Thursday per constraint below
    FRI: [(hm(9, 0), hm(10, 0)),
          (hm(11, 30), hm(12, 0)),
          (hm(12, 30), hm(13, 0)),
          (hm(14, 30), hm(15, 0))]
}

megan_busy = {
    MON: [(hm(9, 0), hm(17, 0))],
    TUE: [(hm(9, 0), hm(9, 30)),
          (hm(10, 0), hm(10, 30)),
          (hm(12, 0), hm(14, 0)),
          (hm(15, 0), hm(15, 30)),
          (hm(16, 0), hm(16, 30))],
    WED: [(hm(9, 30), hm(10, 30)),
          (hm(11, 0), hm(11, 30)),
          (hm(12, 30), hm(13, 0)),
          (hm(13, 30), hm(14, 30)),
          (hm(15, 30), hm(17, 0))],
    THU: [(hm(9, 0), hm(10, 30)),
          (hm(11, 30), hm(14, 0)),
          (hm(14, 30), hm(15, 0)),
          (hm(15, 30), hm(16, 30))],
    FRI: [(hm(9, 0), hm(17, 0))]
}

def add_no_overlap_constraints(s, day_var, start_var, end_var, day_idx, intervals):
    # For each busy interval on this day, enforce no overlap: end <= busy_start OR start >= busy_end
    for (bs, be) in intervals:
        s.add(Implies(day_var == day_idx, Or(end_var <= bs, start_var >= be)))

def fmt_time(m):
    h = m // 60
    mm = m % 60
    return f"{h:02d}:{mm:02d}"

def main():
    # Variables
    day = Int("day")            # 0..4 (Mon..Fri)
    start = Int("start_min")    # minutes since 00:00
    end = Int("end_min")        # minutes since 00:00

    s = Solver()

    # Day bounds (Mon..Fri)
    s.add(day >= 0, day <= 4)

    # Meeting within work hours and fixed duration
    s.add(start >= WORK_START, end <= WORK_END, end == start + MEETING_DURATION)

    # Optional: align to 30-minute grid
    s.add(Mod(start, 30) == 0)

    # Additional constraint: Betty cannot meet on Wednesday and Thursday
    s.add(day != WED, day != THU)

    # No overlap with busy intervals for each participant on the selected day
    for d in range(5):
        add_no_overlap_constraints(s, day, start, end, d, betty_busy.get(d, []))
        add_no_overlap_constraints(s, day, start, end, d, megan_busy.get(d, []))

    if s.check() != sat:
        raise RuntimeError("No feasible schedule found, but the problem statement guarantees a solution.")

    m = s.model()
    day_val = m[day].as_long()
    start_val = m[start].as_long()
    end_val = m[end].as_long()

    print("SOLUTION:")
    print(f"Day: {DAYS[day_val]}")
    print(f"Start Time: {fmt_time(start_val)} (24-hour format)")
    print(f"End Time: {fmt_time(end_val)} (24-hour format)")

if __name__ == "__main__":
    main()