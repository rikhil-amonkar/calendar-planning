from z3 import Solver, Int, Or, sat

# Meeting duration in minutes (60 minutes)
duration = 60

# Meeting start time variable (in minutes after midnight)
start = Int("start")

# Work hours in minutes: from 9:00 (540) to 17:00 (1020)
WORK_START = 540
WORK_END = 1020

# Days encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday.
candidate_days = [0, 1, 2]

# Busy schedules in minutes

# Laura's busy schedule:
# Monday: 10:00 to 10:30 -> (600,630), 11:30 to 12:00 -> (690,720), 16:30 to 17:00 -> (990,1020)
# Tuesday: 12:30 to 13:30 -> (750,810), 16:30 to 17:00 -> (990,1020)
# Wednesday: 12:00 to 12:30 -> (720,750), 15:30 to 16:00 -> (930,960)
laura_busy = {
    0: [(600, 630), (690, 720), (990, 1020)],
    1: [(750, 810), (990, 1020)],
    2: [(720, 750), (930, 960)]
}

# Megan's busy schedule:
# Monday: 9:00 to 9:30 -> (540,570), 10:30 to 12:30 -> (630,750), 13:30 to 17:00 -> (810,1020)
# Tuesday: 9:00 to 12:00 -> (540,720), 12:30 to 17:00 -> (750,1020)
# Wednesday: 9:00 to 16:30 -> (540,990)
megan_busy = {
    0: [(540, 570), (630, 750), (810, 1020)],
    1: [(540, 720), (750, 1020)],
    2: [(540, 990)]
}

# Helper function to ensure the meeting [start, start+duration)
# does not overlap with a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None       # chosen day (0, 1, or 2)
meeting_start_val = None # meeting start time in minutes after midnight

# Iterate over candidate days in order (Monday, then Tuesday, then Wednesday)
for day in candidate_days:
    solver = Solver()
    # The meeting must be entirely within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Laura's busy constraints for the current day
    for busy_start, busy_end in laura_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Add Megan's busy constraints for the current day
    for busy_start, busy_end in megan_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Check for the earliest valid start time on this day
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t)
        if solver.check() == sat:
            meeting_start_val = t
            meeting_day = day
            found = True
            solver.pop()  # Remove the temporary constraint
            break
        solver.pop()
    
    if found:
        break

if found:
    meeting_end_val = meeting_start_val + duration
    start_hour, start_min = divmod(meeting_start_val, 60)
    end_hour, end_min = divmod(meeting_end_val, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
    print(f"A valid meeting time is on {day_names[meeting_day]} from {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")