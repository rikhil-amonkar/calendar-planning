from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30  # meeting duration in minutes
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Days encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday
# George's preferences:
#   - He would rather not meet on Monday.
#   - He would rather not meet on Tuesday after 15:00, so on Tuesday the meeting must finish by 15:00.
#   - He would rather not meet on Wednesday.
# Thus we restrict the meeting to Tuesday with start+duration <= 15:00 (900 minutes).
all_days = [0, 1, 2]

# George's busy schedule in minutes from midnight:
# Monday:    9:30-10:00 -> (570,600), 10:30-11:00 -> (630,660)
# Tuesday:   9:00-10:00 -> (540,600), 13:00-14:00 -> (780,840), 15:00-15:30 -> (900,930)
# Wednesday: 10:00-11:00 -> (600,660), 12:00-12:30 -> (720,750), 14:30-15:00 -> (870,900), 16:00-16:30 -> (960,990)
george_busy = {
    0: [(570, 600), (630, 660)],
    1: [(540, 600), (780, 840), (900, 930)],
    2: [(600, 660), (720, 750), (870, 900), (960, 990)]
}

# Jose's busy schedule in minutes from midnight:
# Monday:    9:00-10:30 -> (540,630), 11:00-12:30 -> (660,750), 13:00-13:30 -> (780,810),
#            14:30-15:00 -> (870,900), 16:00-17:00 -> (960,1020)
# Tuesday:   9:00-10:00 -> (540,600), 11:00-12:00 -> (660,720), 12:30-13:00 -> (750,780),
#            15:00-15:30 -> (900,930), 16:30-17:00 -> (990,1020)
# Wednesday: 10:00-11:00 -> (600,660), 12:30-14:00 -> (750,840),
#            14:30-15:00 -> (870,900), 15:30-17:00 -> (930,1020)
jose_busy = {
    0: [(540, 630), (660, 750), (780, 810), (870, 900), (960, 1020)],
    1: [(540, 600), (660, 720), (750, 780), (900, 930), (990, 1020)],
    2: [(600, 660), (750, 840), (870, 900), (930, 1020)]
}

# Helper function: the meeting interval [start, start+duration) must not overlap with a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None       # will hold the day (0, 1, or 2) when the meeting is scheduled
meeting_start_val = None # meeting start time in minutes from midnight

# We loop over candidate days and enforce George's preferences:
#   - Monday (day 0): not allowed
#   - Tuesday (day 1): meeting must finish by 15:00 (900 minutes)
#   - Wednesday (day 2): not allowed.
for day in all_days:
    solver = Solver()
    
    # Meeting must be within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Apply George's preferences.
    if day == 0:
        # George would rather not meet on Monday.
        solver.add(False)
    elif day == 1:
        # On Tuesday, the meeting must finish by 15:00.
        solver.add(start + duration <= 15 * 60)
    elif day == 2:
        # George would rather not meet on Wednesday.
        solver.add(False)

    # Add George's busy constraints for this day.
    for busy_start, busy_end in george_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Add Jose's busy constraints for this day.
    for busy_start, busy_end in jose_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Search for the earliest possible start time (minute-by-minute within work hours)
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t)
        if solver.check() == sat:
            meeting_start_val = t
            meeting_day = day
            found = True
            solver.pop()
            break
        solver.pop()
    
    if found:
        break

if found:
    meeting_end_val = meeting_start_val + duration
    # Convert minutes into HH:MM format.
    start_hour, start_min = divmod(meeting_start_val, 60)
    end_hour, end_min = divmod(meeting_end_val, 60)
    day_name = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}.get(meeting_day, "Unknown")
    print(f"A valid meeting time is on {day_name} from {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")