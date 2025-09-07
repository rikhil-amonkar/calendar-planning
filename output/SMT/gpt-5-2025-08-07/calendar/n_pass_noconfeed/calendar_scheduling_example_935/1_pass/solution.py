from z3 import *

# Meeting parameters
DURATION = 30  # minutes
WORK_START = 9 * 60
WORK_END = 17 * 60
DAY_MINUTES = WORK_END - WORK_START  # 480

# Days mapping
days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]

def hm_to_offset(h, m):
    return (h * 60 + m) - WORK_START

def no_overlap(start, dur, bstart, bend):
    # meeting [start, start+dur) does not overlap busy [bstart, bend)
    return Or(start + dur <= bstart, start >= bend)

# Busy schedules in minutes offset from 09:00 (i.e., 09:00 -> 0)
Terry_busy = {
    0: [(hm_to_offset(10,30), hm_to_offset(11,0)),
        (hm_to_offset(12,30), hm_to_offset(14,0)),
        (hm_to_offset(15,0),  hm_to_offset(17,0))],
    1: [(hm_to_offset(9,30),  hm_to_offset(10,0)),
        (hm_to_offset(10,30), hm_to_offset(11,0)),
        (hm_to_offset(14,0),  hm_to_offset(14,30)),
        (hm_to_offset(16,0),  hm_to_offset(16,30))],
    2: [(hm_to_offset(9,30),  hm_to_offset(10,30)),
        (hm_to_offset(11,0),  hm_to_offset(12,0)),
        (hm_to_offset(13,0),  hm_to_offset(13,30)),
        (hm_to_offset(15,0),  hm_to_offset(16,0)),
        (hm_to_offset(16,30), hm_to_offset(17,0))],
    3: [(hm_to_offset(9,30),  hm_to_offset(10,0)),
        (hm_to_offset(12,0),  hm_to_offset(12,30)),
        (hm_to_offset(13,0),  hm_to_offset(14,30)),
        (hm_to_offset(16,0),  hm_to_offset(16,30))],
    4: [(hm_to_offset(9,0),   hm_to_offset(11,30)),
        (hm_to_offset(12,0),  hm_to_offset(12,30)),
        (hm_to_offset(13,30), hm_to_offset(16,0)),
        (hm_to_offset(16,30), hm_to_offset(17,0))],
}

Frances_busy = {
    0: [(hm_to_offset(9,30),  hm_to_offset(11,0)),
        (hm_to_offset(11,30), hm_to_offset(13,0)),
        (hm_to_offset(14,0),  hm_to_offset(14,30)),
        (hm_to_offset(15,0),  hm_to_offset(16,0))],
    1: [(hm_to_offset(9,0),   hm_to_offset(9,30)),
        (hm_to_offset(10,0),  hm_to_offset(10,30)),
        (hm_to_offset(11,0),  hm_to_offset(12,0)),
        (hm_to_offset(13,0),  hm_to_offset(14,30)),
        (hm_to_offset(15,30), hm_to_offset(16,30))],
    2: [(hm_to_offset(9,30),  hm_to_offset(10,0)),
        (hm_to_offset(10,30), hm_to_offset(11,0)),
        (hm_to_offset(11,30), hm_to_offset(16,0)),
        (hm_to_offset(16,30), hm_to_offset(17,0))],
    3: [(hm_to_offset(11,0),  hm_to_offset(12,30)),
        (hm_to_offset(14,30), hm_to_offset(17,0))],
    4: [(hm_to_offset(9,30),  hm_to_offset(10,30)),
        (hm_to_offset(11,0),  hm_to_offset(12,30)),
        (hm_to_offset(13,0),  hm_to_offset(16,0)),
        (hm_to_offset(16,30), hm_to_offset(17,0))],
}

# Z3 variables
day = Int("day")        # 0..4 (Mon..Fri)
start = Int("start")    # minutes offset from 09:00, 0..450

opt = Optimize()

# Domain constraints
opt.add(day >= 0, day <= 4)
opt.add(start >= 0, start + DURATION <= DAY_MINUTES)

# Availability constraints per participant
for d in range(5):
    for (bs, be) in Terry_busy[d]:
        opt.add(Implies(day == d, no_overlap(start, DURATION, bs, be)))
    for (bs, be) in Frances_busy[d]:
        opt.add(Implies(day == d, no_overlap(start, DURATION, bs, be)))

# Preferences:
# 1) Avoid Tuesday if possible (soft): penalize choosing Tuesday heavily
# 2) Earliest availability otherwise: earlier day first, then earlier time
tuesday_penalty = If(day == 1, 1, 0)  # 1 if Tuesday, else 0

# Cost = Large penalty for Tuesday + weekly position (day) + time within day
# Weights ensure preference order: avoid Tuesday (dominant), then earliest day, then earliest time
cost = tuesday_penalty * 10000 + day * 1440 + start
opt.minimize(cost)

if opt.check() != sat:
    raise RuntimeError("No feasible schedule found")
m = opt.model()

chosen_day = m[day].as_long()
chosen_start = m[start].as_long()
chosen_end = chosen_start + DURATION

# Convert offsets back to HH:MM
def offset_to_hm(off):
    total = WORK_START + off
    hh = total // 60
    mm = total % 60
    return f"{hh:02d}:{mm:02d}"

start_str = offset_to_hm(chosen_start)
end_str = offset_to_hm(chosen_end)

print(f"{days[chosen_day]} {{{start_str}:{end_str}}}")