from z3 import Solver, Int, Or, sat

# Meeting duration: 30 minutes
duration = 30

# Define the meeting start time variable (in minutes from midnight).
start = Int("start")

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Define the days:
# 0 = Monday, 1 = Tuesday, 2 = Wednesday.
#
# Preferences:
# • Barbara would rather not meet on Monday or Tuesday.
#   (So Wednesday is preferred.)
# • Danielle would like to avoid meetings on Wednesday before 16:30.
#
# We use candidate day ordering to enforce preferences:
# Try Wednesday first. If that fails, try Tuesday then Monday.
candidate_days = [2, 1, 0]

# Danielle's busy schedule (times in minutes):
# Monday:
#   11:00-11:30 -> (660, 690)
#   12:00-12:30 -> (720, 750)
#   15:00-16:00 -> (900, 960)
# Tuesday:
#   9:00-9:30   -> (540, 570)
#   12:30-13:00 -> (750, 780)
#   15:00-15:30 -> (900, 930)
#   16:00-16:30 -> (960, 990)
# Wednesday:
#   9:00-9:30   -> (540, 570)
#   10:30-11:30 -> (630, 690)
#   12:00-12:30 -> (720, 750)
#   13:30-14:00 -> (810, 840)
#   14:30-15:30 -> (870, 930)
#   16:00-16:30 -> (960, 990)
danielle_busy = {
    0: [(660, 690), (720, 750), (900, 960)],
    1: [(540, 570), (750, 780), (900, 930), (960, 990)],
    2: [(540, 570), (630, 690), (720, 750), (810, 840), (870, 930), (960, 990)]
}

# Barbara's busy schedule (times in minutes):
# Monday:
#   9:00-9:30   -> (540, 570)
#   10:00-11:00 -> (600, 660)
#   11:30-12:00 -> (690, 720)
#   12:30-13:00 -> (750, 780)
#   15:00-17:00 -> (900, 1020)
# Tuesday:
#   10:00-10:30 -> (600, 630)
#   11:00-13:00 -> (660, 780)
#   13:30-15:30 -> (810, 930)
#   16:00-17:00 -> (960, 1020)
# Wednesday:
#   10:30-11:00 -> (630, 660)
#   11:30-12:00 -> (690, 720)
#   12:30-13:00 -> (750, 780)
#   13:30-14:00 -> (810, 840)
#   15:00-15:30 -> (900, 930)
#   16:00-16:30 -> (960, 990)
barbara_busy = {
    0: [(540, 570), (600, 660), (690, 720), (750, 780), (900, 1020)],
    1: [(600, 630), (660, 780), (810, 930), (960, 1020)],
    2: [(630, 660), (690, 720), (750, 780), (810, 840), (900, 930), (960, 990)]
}

# Helper function:
# For a busy interval [b_start, b_end), the meeting [start, start+duration)
# must either finish by b_start or start at or after b_end.
def non_overlap(b_start, b_end):
    return Or(start + duration <= b_start, start >= b_end)

found = False
selected_day = None
selected_start = None

# Try each candidate day in the order of preference.
for day in candidate_days:
    solver = Solver()

    # Meeting must be entirely within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)

    # Impose busy constraints for Danielle on the given day.
    for b_start, b_end in danielle_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Impose busy constraints for Barbara on the given day.
    for b_start, b_end in barbara_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Add additional preference for Danielle:
    # On Wednesday (day 2), she wants to avoid meetings before 16:30.
    if day == 2:
        solver.add(start >= 16 * 60 + 30)  # 16:30 -> 990 minutes

    # Check each minute in the work day for a valid start time.
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t)
        if solver.check() == sat:
            selected_start = t
            selected_day = day
            found = True
            solver.pop()  # pop the current push before breaking out
            break
        solver.pop()

    if found:
        break

if found:
    selected_end = selected_start + duration
    # Convert minutes to HH:MM format.
    start_hr, start_min = divmod(selected_start, 60)
    end_hr, end_min = divmod(selected_end, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(day_names[selected_day], start_hr, start_min, end_hr, end_min))
else:
    print("No valid meeting time could be found that meets all the constraints.")