from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30  # meeting duration in minutes (half an hour)
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Days encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday
candidate_days = [0, 1, 2]

# Christine's busy schedule in minutes from midnight:
# Monday:   15:00 to 15:30 -> (900, 930), 16:00 to 16:30 -> (960, 990)
# Tuesday:  9:30 to 10:00   -> (570, 600)
# Wednesday: 12:00 to 12:30 -> (720, 750), 13:30 to 14:00 -> (810, 840), 15:30 to 16:00 -> (930, 960)
christine_busy = {
    0: [(900, 930), (960, 990)],
    1: [(570, 600)],
    2: [(720, 750), (810, 840), (930, 960)]
}

# Jose's busy schedule in minutes from midnight:
# Monday:   9:00 to 10:30  -> (540, 630), 11:00 to 11:30 -> (660, 690),
#           12:30 to 14:30 -> (750, 870), 15:00 to 17:00 -> (900, 1020)
# Tuesday:  9:30 to 13:30  -> (570, 810), 14:00 to 16:00 -> (840, 960), 16:30 to 17:00 -> (990, 1020)
# Wednesday: 10:00 to 10:30 -> (600, 630), 11:00 to 13:30 -> (660, 810),
#            14:00 to 14:30 -> (840, 870), 15:00 to 15:30 -> (900, 930), 16:30 to 17:00 -> (990, 1020)
jose_busy = {
    0: [(540, 630), (660, 690), (750, 870), (900, 1020)],
    1: [(570, 810), (840, 960), (990, 1020)],
    2: [(600, 630), (660, 810), (840, 870), (900, 930), (990, 1020)]
}

# Helper function: ensures that the meeting [start, start+duration) does not overlap
# with a busy interval [busy_start, busy_end).
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None       # day when meeting is scheduled (0,1,2)
meeting_start_val = None # meeting start time in minutes from midnight

# Try candidate days in order, aiming for earliest overall availability.
for day in candidate_days:
    solver = Solver()
    
    # The meeting must fully fall within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Christine's busy constraints for the day
    for busy_interval in christine_busy.get(day, []):
        busy_start, busy_end = busy_interval
        solver.add(non_overlap(busy_start, busy_end))
    
    # Add Jose's busy constraints for the day
    for busy_interval in jose_busy.get(day, []):
        busy_start, busy_end = busy_interval
        solver.add(non_overlap(busy_start, busy_end))
    
    # Find the earliest available time slot minute-by-minute
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
    start_hour, start_min = divmod(meeting_start_val, 60)
    end_hour, end_min = divmod(meeting_end_val, 60)
    day_name = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}.get(meeting_day, "Unknown")
    print(f"A valid meeting time is on {day_name} from {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")