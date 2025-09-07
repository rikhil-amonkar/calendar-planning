from z3 import *

# Meeting parameters
DURATION = 30  # minutes
WORK_START = 9 * 60       # 09:00 in minutes
WORK_END = 17 * 60        # 17:00 in minutes
DAY_WINDOW = WORK_END - WORK_START  # 480 minutes

# Days: 0=Monday, 1=Tuesday, 2=Wednesday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}

# Helper to convert absolute minutes to minutes-from-09:00
def rel(t_min):
    return t_min - WORK_START

# Busy schedules per participant (absolute minutes), then converted to relative minutes from 09:00
# Joshua:
joshua_busy = {
    0: [(15*60, 15*60+30)],
    1: [(11*60+30, 12*60), (13*60, 13*60+30), (14*60+30, 15*60)],
    2: []
}
# Joyce:
joyce_busy = {
    0: [(9*60, 9*60+30), (10*60, 11*60), (11*60+30, 12*60+30), (13*60, 15*60), (15*60+30, 17*60)],
    1: [(9*60, 17*60)],
    2: [(9*60, 9*60+30), (10*60, 11*60), (12*60+30, 15*60+30), (16*60, 16*60+30)]
}

# Convert to relative times (minutes from 09:00)
def to_relative(day_busy):
    rel_busy = {}
    for d, intervals in day_busy.items():
        rel_busy[d] = [(rel(s), rel(e)) for (s, e) in intervals]
    return rel_busy

joshua_busy_rel = to_relative(joshua_busy)
joyce_busy_rel = to_relative(joyce_busy)

# Z3 variables
day = Int("day")                 # 0..2
start = Int("start")             # minutes from 09:00
end = start + DURATION

opt = Optimize()

# Domain constraints
opt.add(And(day >= 0, day <= 2))
opt.add(start >= 0)
opt.add(end <= DAY_WINDOW)
# 30-minute granularity
opt.add(start % 30 == 0)

# Non-overlap constraints for both participants on the selected day
def add_non_overlap(person_busy):
    for d in [0, 1, 2]:
        for (bs, be) in person_busy[d]:
            # Meeting [start, end) must not intersect [bs, be)
            opt.add(Implies(day == d, Or(end <= bs, start >= be)))

add_non_overlap(joshua_busy_rel)
add_non_overlap(joyce_busy_rel)

# Preferences:
# 1) Joyce would rather not meet on Monday before 12:00 (i.e., avoid day==0 and start < 180)
opt.add_soft(Not(And(day == 0, start < (12*60 - WORK_START))), weight=1, id="avoid_mon_before_noon")
# 2) Prefer Wednesday if possible
opt.add_soft(day == 2, weight=1, id="prefer_wed")
# As a tie-breaker, choose the earliest start time
opt.minimize(start)

if opt.check() == sat:
    m = opt.model()
    chosen_day = m[day].as_long()
    chosen_start_rel = m[start].as_long()
    chosen_start_abs = WORK_START + chosen_start_rel
    chosen_end_abs = chosen_start_abs + DURATION

    def fmt(t):
        hh = t // 60
        mm = t % 60
        return f"{hh:02d}:{mm:02d}"

    day_str = day_names[chosen_day]
    start_str = fmt(chosen_start_abs)
    end_str = fmt(chosen_end_abs)

    # Output includes both day of week and time range in {HH:MM:HH:MM} format
    print(day_str)
    print(f"{{{start_str}:{end_str}}}")
else:
    print("No feasible meeting time found.")