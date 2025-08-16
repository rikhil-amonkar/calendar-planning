from z3 import *

def minutes(hh_mm):
    hh, mm = map(int, hh_mm.split(":"))
    return hh * 60 + mm

def format_time(m):
    hh = m // 60
    mm = m % 60
    return f"{hh:02d}:{mm:02d}"

# Problem data
work_start = minutes("09:00")
work_end = minutes("17:00")
duration = 30  # minutes

# Day encoding
MONDAY = 0
TUESDAY = 1
day_names = {MONDAY: "Monday", TUESDAY: "Tuesday"}

# Busy schedules as (start_min, end_min) per day
margaret_busy = {
    MONDAY: [
        (minutes("10:30"), minutes("11:00")),
        (minutes("11:30"), minutes("12:00")),
        (minutes("13:00"), minutes("13:30")),
        (minutes("15:00"), minutes("17:00")),
    ],
    TUESDAY: [
        (minutes("12:00"), minutes("12:30")),
    ],
}

alexis_busy = {
    MONDAY: [
        (minutes("09:30"), minutes("11:30")),
        (minutes("12:30"), minutes("13:00")),
        (minutes("14:00"), minutes("17:00")),
    ],
    TUESDAY: [
        (minutes("09:00"), minutes("09:30")),
        (minutes("10:00"), minutes("10:30")),
        (minutes("14:00"), minutes("16:30")),
    ],
}

# Z3 variables
day = Int("day")            # 0 = Monday, 1 = Tuesday
start = Int("start")        # minutes from 00:00 on the chosen day
end = Int("end")

s = Solver()

# Domain constraints
s.add(Or(day == MONDAY, day == TUESDAY))
s.add(end == start + duration)
s.add(start >= work_start, end <= work_end)

# Preferences:
# Margaret does not want to meet on Monday nor on Tuesday before 14:30
s.add(day != MONDAY)  # Not Monday
s.add(Implies(day == TUESDAY, start >= minutes("14:30")))

# No-overlap with busy slots
def add_no_overlap(schedule):
    for d, intervals in schedule.items():
        for (bs, be) in intervals:
            # meeting [start, end) does not overlap [bs, be)
            s.add(Implies(day == d, Or(end <= bs, start >= be)))

add_no_overlap(margaret_busy)
add_no_overlap(alexis_busy)

if s.check() != sat:
    raise RuntimeError("No solution found, but the problem statement guarantees one.")

m = s.model()
day_val = m[day].as_long()
start_val = m[start].as_long()
end_val = start_val + duration

print("SOLUTION:")
print(f"Day: {day_names[day_val]}")
print(f"Start Time: {format_time(start_val)}")
print(f"End Time: {format_time(end_val)}")