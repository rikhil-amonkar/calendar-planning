from z3 import *

def minutes(h, m):
    return (h - 9) * 60 + m  # relative to 09:00

# Create solver with optimization (to honor preferences and choose earliest feasible time)
opt = Optimize()

# Variables
day = Int('day')           # 0 = Monday, 1 = Tuesday
start = Int('start')       # minutes from 09:00
end = Int('end')

# Constants
MEETING_DURATION = 30
WORK_START = 0             # 09:00
WORK_END = 8 * 60          # 17:00

# Domain constraints
opt.add(Or(day == 0, day == 1))
opt.add(start >= WORK_START, end == start + MEETING_DURATION, end <= WORK_END)
opt.add(Mod(start, 30) == 0)  # align to 30-minute grid

def no_overlap(ms, me, bs, be):
    # Meeting [ms, me) does not overlap busy [bs, be)
    return Or(me <= bs, ms >= be)

# Busy schedules
# Shirley
shirley_busy_monday = [
    (minutes(10, 30), minutes(11, 0)),
    (minutes(12, 0), minutes(12, 30)),
    (minutes(16, 0), minutes(16, 30)),
]
shirley_busy_tuesday = [
    (minutes(9, 30), minutes(10, 0)),
]

# Albert
albert_busy_monday = [
    (minutes(9, 0), minutes(17, 0)),
]
albert_busy_tuesday = [
    (minutes(9, 30), minutes(11, 0)),
    (minutes(11, 30), minutes(12, 30)),
    (minutes(13, 0), minutes(16, 0)),
    (minutes(16, 30), minutes(17, 0)),
]

# Apply non-overlap constraints per day
opt.add(Implies(day == 0, And(*[no_overlap(start, end, s, e) for (s, e) in shirley_busy_monday])))
opt.add(Implies(day == 1, And(*[no_overlap(start, end, s, e) for (s, e) in shirley_busy_tuesday])))

opt.add(Implies(day == 0, And(*[no_overlap(start, end, s, e) for (s, e) in albert_busy_monday])))
opt.add(Implies(day == 1, And(*[no_overlap(start, end, s, e) for (s, e) in albert_busy_tuesday])))

# Preference: Shirley would rather not meet on Tuesday after 10:30
# Softly prefer not (day == Tuesday and start > 10:30)
opt.add_soft(Or(day != 1, start <= minutes(10, 30)), weight=1, id='prefer_not_after_1030_tuesday')

# Secondary optimization: prefer Monday if possible, then earliest time
opt.minimize(day)
opt.minimize(start)

if opt.check() == sat:
    m = opt.model()
    d = m[day].as_long()
    s = m[start].as_long()
    e = m[end].as_long()

    day_str = "Monday" if d == 0 else "Tuesday"
    def fmt(t):
        h = 9 + (t // 60)
        mnt = t % 60
        return f"{h:02d}:{mnt:02d}"

    print("SOLUTION:")
    print(f"Day: {day_str}")
    print(f"Start Time: {fmt(s)} (24-hour format)")
    print(f"End Time: {fmt(e)} (24-hour format)")
else:
    print("SOLUTION:")
    print("Day: N/A")
    print("Start Time: 00:00 (24-hour format)")
    print("End Time: 00:00 (24-hour format)")