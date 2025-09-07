from z3 import *

# Time constants
WORK_START = 9 * 60  # 09:00 in minutes from midnight
WORK_END = 17 * 60   # 17:00 in minutes from midnight
DAY_START_OFFSET = WORK_START  # Base for conversion
MEETING_DURATION = 30  # minutes
SLOT_GRANULARITY = 30  # minutes
DAY_NAMES = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]

# Represent times within the day as minutes offset from 09:00 (0..480)
def t(hh, mm):
    return (hh * 60 + mm) - DAY_START_OFFSET

# Busy schedules per person per day (0=Mon ... 4=Fri), times in minutes from 09:00
busy = {
    "Daniel": {
        0: [(t(9,30), t(10,30)), (t(12,0), t(12,30)), (t(13,0), t(14,0)),
            (t(14,30), t(15,0)), (t(15,30), t(16,0))],
        1: [(t(11,0), t(12,0)), (t(13,0), t(13,30)), (t(15,30), t(16,0)), (t(16,30), t(17,0))],
        2: [(t(9,0), t(10,0)), (t(14,0), t(14,30))],
        3: [(t(10,30), t(11,0)), (t(12,0), t(13,0)), (t(14,30), t(15,0)), (t(15,30), t(16,0))],
        4: [(t(9,0), t(9,30)), (t(11,30), t(12,0)), (t(13,0), t(13,30)), (t(16,30), t(17,0))],
    },
    "Bradley": {
        0: [(t(9,30), t(11,0)), (t(11,30), t(12,0)), (t(12,30), t(13,0)), (t(14,0), t(15,0))],
        1: [(t(10,30), t(11,0)), (t(12,0), t(13,0)), (t(13,30), t(14,0)), (t(15,30), t(16,30))],
        2: [(t(9,0), t(10,0)), (t(11,0), t(13,0)), (t(13,30), t(14,0)), (t(14,30), t(17,0))],
        3: [(t(9,0), t(12,30)), (t(13,30), t(14,0)), (t(14,30), t(15,0)), (t(15,30), t(16,30))],
        4: [(t(9,0), t(9,30)), (t(10,0), t(12,30)), (t(13,0), t(13,30)), (t(14,0), t(14,30)), (t(15,30), t(16,30))],
    }
}

# Z3 variables
day = Int('day')       # 0..4 => Monday..Friday
start = Int('start')   # minutes from 09:00 within [0..480)

s = Solver()

# Domain constraints
s.add(day >= 0, day <= 4)
s.add(start >= 0, start <= (WORK_END - WORK_START) - MEETING_DURATION)
s.add(start % SLOT_GRANULARITY == 0)

# Non-overlap constraints for each participant on the chosen day
def no_overlap_for(person):
    constraints = []
    for d in range(5):
        daily = busy[person][d]
        # For each busy interval, ensure meeting [start, start+duration) doesn't overlap when day == d
        day_constraints = [Or(start + MEETING_DURATION <= b_start, start >= b_end) for (b_start, b_end) in daily]
        constraints.append(Implies(day == d, And(day_constraints) if day_constraints else True))
    return And(constraints)

s.add(no_overlap_for("Daniel"))
s.add(no_overlap_for("Bradley"))

# Preferences/constraints:
# Daniel would rather not meet on Wednesday or Thursday (treat as hard constraints)
s.add(day != 2)  # Wednesday
s.add(day != 3)  # Thursday

# Bradley does not want to meet on Monday, Tuesday before 12:00, or Friday (treat as hard constraints)
s.add(day != 0)  # Monday
s.add(day != 4)  # Friday
# If Tuesday, then not before 12:00 (12:00 => 180 minutes from 09:00)
s.add(Implies(day == 1, start >= t(12, 0)))

# Helper to convert offset minutes (from 09:00) to HH:MM
def to_hhmm(offset_minutes):
    total = DAY_START_OFFSET + offset_minutes
    hh = total // 60
    mm = total % 60
    return f"{hh:02d}:{mm:02d}"

if s.check() == sat:
    m = s.model()
    d = m[day].as_long()
    st = m[start].as_long()
    en = st + MEETING_DURATION
    day_name = DAY_NAMES[d]
    time_range = f"{to_hhmm(st)}:{to_hhmm(en)}"
    print(f"{day_name} {{{time_range}}}")
else:
    print("No valid meeting time found.")