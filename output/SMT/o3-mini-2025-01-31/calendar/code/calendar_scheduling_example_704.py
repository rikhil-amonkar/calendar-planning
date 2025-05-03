from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30  # meeting duration in minutes
start = Int("start")  # meeting start time (in minutes from midnight)

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Days mapping: 0 = Monday, 1 = Tuesday, 2 = Wednesday

# Larry's calendar is wide open (no busy intervals)

# Samuel's busy schedule (times in minutes):
# Monday (day 0):
#   10:30 to 11:00 => (630,660)
#   12:00 to 12:30 => (720,750)
#   13:00 to 15:00 => (780,900)
#   15:30 to 16:30 => (930,990)
# Tuesday (day 1):
#   9:00 to 12:00  => (540,720)
#   14:00 to 15:30 => (840,930)
#   16:30 to 17:00 => (990,1020)
# Wednesday (day 2):
#   10:30 to 11:00 => (630,660)
#   11:30 to 12:00 => (690,720)
#   12:30 to 13:00 => (750,780)
#   14:00 to 14:30 => (840,870)
#   15:00 to 16:00 => (900,960)
samuel_busy = {
    0: [(630,660), (720,750), (780,900), (930,990)],
    1: [(540,720), (840,930), (990,1020)],
    2: [(630,660), (690,720), (750,780), (840,870), (900,960)]
}

# Preferences:
# - Larry would rather not meet on Wednesday (day 2).
# - Samuel would like to avoid more meetings on Tuesday (day 1).
#
# To incorporate these "avoid" preferences while still finding a solution if necessary,
# we first try to schedule the meeting on "preferred" days,
# and only if no solution is found do we fallback to the less preferred days.
#
# In this case, the only day that is free of avoidance is Monday (day 0).
# So we try Monday first. If a valid slot exists on Monday, we choose it as it is the earliest
# availability overall. If not, we then try Tuesday (day 1) and then Wednesday (day 2).

def non_overlap(busy_start, busy_end):
    # The meeting interval [start, start+duration) must not overlap with [busy_start, busy_end)
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None   # 0 = Monday, 1 = Tuesday, 2 = Wednesday
meeting_start = None

# Define our prioritized day ordering:
# Preferred days (no avoid): Monday (day 0)
preferred_days = [0]
# Fallback days: Tuesday (day 1) is avoided by Samuel and Wednesday (day 2) is avoided by Larry.
fallback_days = [1, 2]

# First, try preferred days.
for day in preferred_days:
    solver = Solver()
    # Meeting must be within the workday.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Samuel's busy constraints for the day.
    for b_start, b_end in samuel_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # No busy constraints for Larry since his calendar is open.
    
    # Try possible meeting start times in ascending order.
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t)
        if solver.check() == sat:
            meeting_start = t
            meeting_day = day
            found = True
            solver.pop()
            break
        solver.pop()
    if found:
        break

# If no solution is found on preferred days, try fallback days.
if not found:
    for day in fallback_days:
        solver = Solver()
        solver.add(start >= WORK_START, start + duration <= WORK_END)
        # Add Samuel's busy constraints.
        for b_start, b_end in samuel_busy.get(day, []):
            solver.add(non_overlap(b_start, b_end))
        # No constraints for Larry.
    
        for t in range(WORK_START, WORK_END - duration + 1):
            solver.push()
            solver.add(start == t)
            if solver.check() == sat:
                meeting_start = t
                meeting_day = day
                found = True
                solver.pop()
                break
            solver.pop()
        if found:
            break

if found:
    meeting_end = meeting_start + duration
    # Convert minutes to HH:MM format.
    start_hour, start_min = divmod(meeting_start, 60)
    end_hour, end_min = divmod(meeting_end, 60)
    day_str = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}[meeting_day]
    print(f"A valid meeting time is on {day_str} from {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")