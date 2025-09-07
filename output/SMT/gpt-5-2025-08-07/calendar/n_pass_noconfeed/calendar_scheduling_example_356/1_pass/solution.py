# Requires: z3-solver (pip install z3-solver)

from z3 import *

def hm(h, m):
    return h * 60 + m

def to_hhmm(total_minutes):
    h = total_minutes // 60
    m = total_minutes % 60
    return f"{h:02d}:{m:02d}"

def main():
    # Day and work window
    day = "Monday"
    work_start = hm(9, 0)    # 09:00
    work_end   = hm(17, 0)   # 17:00
    duration   = 30          # 30 minutes

    # Busy intervals (absolute minutes, [start, end), end-exclusive)
    Katherine = [(hm(12, 0), hm(12, 30)),
                 (hm(13, 0), hm(14, 30))]
    Rebecca = []  # no meetings
    Julie = [(hm(9, 0), hm(9, 30)),
             (hm(10, 30), hm(11, 0)),
             (hm(13, 30), hm(14, 0)),
             (hm(15, 0), hm(15, 30))]
    Angela = [(hm(9, 0), hm(10, 0)),
              (hm(10, 30), hm(11, 0)),
              (hm(11, 30), hm(14, 0)),
              (hm(14, 30), hm(15, 0)),
              (hm(16, 30), hm(17, 0))]
    Nicholas = [(hm(9, 30), hm(11, 0)),
                (hm(11, 30), hm(13, 30)),
                (hm(14, 0), hm(16, 0)),
                (hm(16, 30), hm(17, 0))]
    Carl = [(hm(9, 0), hm(11, 0)),
            (hm(11, 30), hm(12, 30)),
            (hm(13, 0), hm(14, 30)),
            (hm(15, 0), hm(16, 0)),
            (hm(16, 30), hm(17, 0))]

    all_busy = {
        "Katherine": Katherine,
        "Rebecca": Rebecca,
        "Julie": Julie,
        "Angela": Angela,
        "Nicholas": Nicholas,
        "Carl": Carl
    }

    s = Int("start")  # start time in absolute minutes from 00:00

    opt = Optimize()

    # Work hours and granularity (30-minute boundaries)
    opt.add(s >= work_start)
    opt.add(s + duration <= work_end)
    opt.add(s % 30 == 0)

    # No overlap with each participant's busy times
    def no_overlap(start_var, busy_interval):
        a, b = busy_interval
        # meeting [s, s+duration) does not intersect [a, b)
        return Or(start_var + duration <= a, start_var >= b)

    for person, intervals in all_busy.items():
        for interval in intervals:
            opt.add(no_overlap(s, interval))

    # Preference: Angela would like to avoid meetings before 15:00
    prefer_after_1500 = s >= hm(15, 0)
    opt.add_soft(prefer_after_1500, weight="1", id="AngelaPref")

    # Additionally, among solutions that respect the preference, choose the earliest time
    opt.minimize(s)

    if opt.check() == sat:
        m = opt.model()
        start_val = m.evaluate(s).as_long()
        end_val = start_val + duration
        start_str = to_hhmm(start_val)
        end_str = to_hhmm(end_val)

        print(day)
        print(f"{{{start_str}:{end_str}}}")
    else:
        print("No feasible time found.")

if __name__ == "__main__":
    main()