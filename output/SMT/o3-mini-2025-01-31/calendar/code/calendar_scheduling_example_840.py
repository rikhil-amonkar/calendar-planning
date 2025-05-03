from z3 import Solver, Int, Or, sat

# Meeting duration in minutes (60 minutes)
duration = 60

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 9 * 60   # 540 minutes
WORK_END   = 17 * 60  # 1020 minutes

# We'll encode days as: Monday=0, Tuesday=1, Wednesday=2, Thursday=3.
# Note: Steven is busy all day Monday, so our candidate days are Tuesday, Wednesday, and Thursday.
candidate_days = [1, 2, 3]

# Busy intervals for Scott (times in minutes from midnight)
# Tuesday:
#   10:30-11:00 -> (630, 660)
#   11:30-12:00 -> (690, 720)
#   12:30-13:00 -> (750, 780)
#   13:30-14:00 -> (810, 840)
#   14:30-15:00 -> (870, 900)
# Wednesday:
#   9:00-10:00  -> (540, 600)
#   14:00-14:30 -> (840, 870)
#   15:30-16:30 -> (930, 990)
# Thursday:
#   9:30-10:00  -> (570, 600)
#   11:00-12:30 -> (660, 750)
#   14:30-15:00 -> (870, 900)
#   16:30-17:00 -> (990,1020)
scott_busy = {
    1: [(630,660), (690,720), (750,780), (810,840), (870,900)],
    2: [(540,600), (840,870), (930,990)],
    3: [(570,600), (660,750), (870,900), (990,1020)]
}

# Busy intervals for Steven
# Monday: busy 9:00-17:00 (but Monday is not considered)
# Tuesday:
#   9:00-13:00  -> (540,780)
#   13:30-14:30 -> (810,870)
#   15:00-16:30 -> (900,990)
# Wednesday:
#   9:00-14:30  -> (540,870)
#   15:00-17:00 -> (900,1020)
# Thursday:
#   9:30-12:30  -> (570,750)
#   14:00-15:30 -> (840,930)
#   16:30-17:00 -> (990,1020)
steven_busy = {
    1: [(540,780), (810,870), (900,990)],
    2: [(540,870), (900,1020)],
    3: [(570,750), (840,930), (990,1020)]
}

# Additional preference: Steven would rather not meet on Thursday after 14:00.
# We interpret this as: if the meeting is on Thursday (day 3), the meeting must end by 14:00,
# meaning the meeting start time must be <= 13:00 (i.e., 780 minutes).
def add_thursday_preference(s, day):
    if day == 3:
        return s + duration <= 14 * 60  # meeting ends by 14:00 (840 minutes)
    return True

# Utility function: Given a busy interval [b_start, b_end) and meeting start time s,
# ensure that the meeting (lasting 'duration') does NOT overlap with that interval.
def no_overlap(b_start, b_end, s):
    return Or(s + duration <= b_start, s >= b_end)

solution_found = False
selected_day = None
selected_start = None

# Iterate over candidate days in the specified order for earliest availability.
for day in candidate_days:
    solver = Solver()
    s = Int("s")  # s is the meeting start time (in minutes from midnight)

    # The meeting must fit inside the workday.
    solver.add(s >= WORK_START, s + duration <= WORK_END)
    
    # Add the additional preference for Thursday.
    if day == 3:
        solver.add(s + duration <= 14 * 60)  # meeting ends by 14:00
    
    # Add Scott's busy intervals for the current day.
    for (b_start, b_end) in scott_busy.get(day, []):
        solver.add(no_overlap(b_start, b_end, s))
    
    # Add Steven's busy intervals for the current day.
    for (b_start, b_end) in steven_busy.get(day, []):
        solver.add(no_overlap(b_start, b_end, s))
    
    # Search for the earliest possible meeting time by trying each minute.
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(s == t)
        if solver.check() == sat:
            selected_start = t
            selected_day = day
            solution_found = True
            solver.pop()
            break
        solver.pop()
    
    if solution_found:
        break

if solution_found:
    selected_end = selected_start + duration
    # Convert minutes back to HH:MM
    start_hour, start_minute = divmod(selected_start, 60)
    end_hour, end_minute = divmod(selected_end, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(day_names[selected_day], start_hour, start_minute, end_hour, end_minute))
else:
    print("No valid meeting time could be found that satisfies all constraints.")