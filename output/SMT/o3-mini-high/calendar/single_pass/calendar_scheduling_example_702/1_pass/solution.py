from z3 import *

# We represent days as numbers: 0=Monday, 1=Tuesday, 2=Wednesday.
day = Int('day')
# s represents the meeting start time in minutes from midnight.
s = Int('s')

duration = 30  # meeting lasts 30 minutes.
work_start = 9 * 60    # 9:00 = 540 minutes.
work_end = 17 * 60     # 17:00 = 1020 minutes.

# Create an optimizer (so we can choose the earliest time with our objective).
opt = Optimize()
# Constrain the meeting time to be within working hours.
opt.add(s >= work_start, s + duration <= work_end)
# Robert prefers not to have Monday; we restrict the day to Tuesday (1) or Wednesday (2).
opt.add(Or(day == 1, day == 2))

# Helper: no_overlap(interval_start, interval_end) asserts that the meeting does not conflict with a busy slot.
def no_overlap(interval_start, interval_end):
    # Meeting [s, s+duration] does not overlap with busy interval [interval_start, interval_end] if:
    # either meeting ends on or before the busy period starts, or it starts on or after the busy period ends.
    return Or(s + duration <= interval_start, s >= interval_end)

# ---------------------
# Busy intervals (in minutes) for each participant:
#
# Robert:
#   Monday: 11:00–11:30 (660–690), 14:00–14:30 (840–870), 15:30–16:00 (930–960)  [Not used because Monday is avoided]
#   Tuesday: 10:30–11:00 (630–660), 15:00–15:30 (900–930)
#   Wednesday: 10:00–11:00 (600–660), 11:30–12:00 (690–720),
#              12:30–13:00 (750–780), 13:30–14:00 (810–840),
#              15:00–15:30 (900–930), 16:00–16:30 (960–990)
#
# Ralph:
#   Monday: 10:00–13:30 (600–810), 14:00–14:30 (840–870), 15:00–17:00 (900–1020)  [Not used because Monday is avoided]
#   Tuesday: 09:00–09:30 (540–570), 10:00–10:30 (600–630), 11:00–11:30 (660–690),
#            12:00–13:00 (720–780), 14:00–15:30 (840–930), 16:00–17:00 (960–1020)
#   Wednesday: 10:30–11:00 (630–660), 11:30–12:00 (690–720),
#              13:00–14:30 (780–870), 16:30–17:00 (990–1020)

# ---------------------
# Tuesday busy constraints (day == 1):
# Robert’s Tuesday intervals:
opt.add(Implies(day == 1, no_overlap(630, 660)))   # 10:30 – 11:00
opt.add(Implies(day == 1, no_overlap(900, 930)))   # 15:00 – 15:30
# Ralph’s Tuesday intervals:
opt.add(Implies(day == 1, no_overlap(540, 570)))   # 09:00 – 09:30
opt.add(Implies(day == 1, no_overlap(600, 630)))   # 10:00 – 10:30
opt.add(Implies(day == 1, no_overlap(660, 690)))   # 11:00 – 11:30
opt.add(Implies(day == 1, no_overlap(720, 780)))   # 12:00 – 13:00
opt.add(Implies(day == 1, no_overlap(840, 930)))   # 14:00 – 15:30
opt.add(Implies(day == 1, no_overlap(960, 1020)))  # 16:00 – 17:00

# ---------------------
# Wednesday busy constraints (day == 2):
# Robert’s Wednesday intervals:
opt.add(Implies(day == 2, no_overlap(600, 660)))   # 10:00 – 11:00
opt.add(Implies(day == 2, no_overlap(690, 720)))   # 11:30 – 12:00
opt.add(Implies(day == 2, no_overlap(750, 780)))   # 12:30 – 13:00
opt.add(Implies(day == 2, no_overlap(810, 840)))   # 13:30 – 14:00
opt.add(Implies(day == 2, no_overlap(900, 930)))   # 15:00 – 15:30
opt.add(Implies(day == 2, no_overlap(960, 990)))   # 16:00 – 16:30
# Ralph’s Wednesday intervals:
opt.add(Implies(day == 2, no_overlap(630, 660)))   # 10:30 – 11:00
opt.add(Implies(day == 2, no_overlap(690, 720)))   # 11:30 – 12:00
opt.add(Implies(day == 2, no_overlap(780, 870)))   # 13:00 – 14:30
opt.add(Implies(day == 2, no_overlap(990, 1020)))  # 16:30 – 17:00

# ---------------------
# Objective: choose the earliest meeting in the week.
# (Since day is 1 or 2, we “weight” day by 60 minutes. This makes a Tuesday meeting (day=1)
# with a later time still come before any Wednesday meeting (day=2) provided the time offset is less.)
opt.minimize(60 * day + s)

if opt.check() == sat:
    m = opt.model()
    chosen_day = m[day].as_long()
    chosen_start = m[s].as_long()
    
    # Map day numbers to names.
    day_map = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
    day_str = day_map.get(chosen_day, "Unknown")
    
    def to_HHMM(minutes):
        hour = minutes // 60
        minute = minutes % 60
        return f"{hour:02d}:{minute:02d}"
    
    start_str = to_HHMM(chosen_start)
    end_str = to_HHMM(chosen_start + duration)
    
    print("SOLUTION:")
    print("Day:", day_str)
    print("Start Time:", start_str)
    print("End Time:", end_str)
else:
    print("No solution found.")