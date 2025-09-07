from z3 import *

# Meeting parameters
DURATION = 30  # minutes
WORK_START = 9 * 60  # 9:00 in minutes since midnight
WORK_END = 17 * 60   # 17:00 in minutes since midnight

# We will model time within the work window [9:00, 17:00] as minutes offset from 9:00
OFFSET_START = 0
OFFSET_END = WORK_END - WORK_START  # 480 minutes

# Days
days = ["Monday", "Tuesday"]
MON, TUE = 0, 1

# Busy schedules as offsets from 9:00 for each day
# Intervals are [start, end) in minutes relative to 9:00
Shirley_busy = {
    MON: [(90, 120), (180, 210), (420, 450)],   # 10:30-11:00, 12:00-12:30, 16:00-16:30
    TUE: [(30, 60)]                             # 9:30-10:00
}
Albert_busy = {
    MON: [(0, 480)],                            # 9:00-17:00 (all day)
    TUE: [(30, 120), (150, 210), (240, 420), (450, 480)]  # 9:30-11:00, 11:30-12:30, 13:00-16:00, 16:30-17:00
}

# Z3 variables
day = Int('day')        # 0=Monday, 1=Tuesday
start = Int('start')    # start time offset from 9:00 in minutes

opt = Optimize()

# Domain constraints
opt.add(Or(day == MON, day == TUE))
opt.add(start >= OFFSET_START)
opt.add(start + DURATION <= OFFSET_END)

# No-overlap constraints with busy intervals
def add_no_overlap_for_day(busy_list, d_idx):
    for (bs, be) in busy_list:
        # If meeting is on day d_idx, it must not overlap the busy interval
        opt.add(Implies(day == d_idx, Or(start + DURATION <= bs, start >= be)))

add_no_overlap_for_day(Shirley_busy[MON], MON)
add_no_overlap_for_day(Shirley_busy[TUE], TUE)
add_no_overlap_for_day(Albert_busy[MON], MON)
add_no_overlap_for_day(Albert_busy[TUE], TUE)

# Preference: Shirley would rather not meet on Tuesday after 10:30.
# That is, if Tuesday, prefer meeting to end by 10:30 (i.e., start + duration <= 90 minutes from 9:00).
opt.add_soft(Implies(day == TUE, start + DURATION <= 90), weight=1, id="avoid_after_1030_tue")

# Solve
if opt.check() != sat:
    raise RuntimeError("No feasible meeting time found.")

m = opt.model()
d_val = m[day].as_long()
s_val = m[start].as_long()
e_val = s_val + DURATION

# Convert offsets (from 9:00) back to absolute times
def minutes_to_hhmm(total_minutes_from_midnight):
    hh = total_minutes_from_midnight // 60
    mm = total_minutes_from_midnight % 60
    return f"{hh:02d}:{mm:02d}"

abs_start = WORK_START + s_val
abs_end = WORK_START + e_val

start_str = minutes_to_hhmm(abs_start)
end_str = minutes_to_hhmm(abs_end)
day_str = days[d_val]

# Output: include both the time range in {HH:MM:HH:MM} and the day
print(f"{day_str} {{{start_str}:{end_str}}}")