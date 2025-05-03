from z3 import Solver, Int, Or, sat

# Duration of the meeting in minutes (30 minutes)
duration = 30

# Meeting start time variable (in minutes after midnight)
start = Int("start")

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Days encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday.
# Given that Randy cannot meet on Monday and Matthew prefers not to meet on Wednesday,
# we will try candidate days in order: Tuesday first, then Wednesday.
candidate_days = [1, 2]

# Busy schedules for each participant (times expressed in minutes after midnight):

# Matthew's schedule:
# Monday: 9:00-9:30, 10:30-11:30, 13:30-14:00, 15:00-15:30, 16:00-16:30
# Tuesday: 10:30-11:30
# Wednesday: 9:00-9:30, 10:00-11:00, 11:30-12:00, 13:00-14:00, 15:00-15:30, 16:00-16:30
matthew_busy = {
    0: [(540, 570), (630, 690), (810, 840), (900, 930), (960, 990)],
    1: [(630, 690)],
    2: [(540, 570), (600, 660), (690, 720), (780, 840), (900, 930), (960, 990)]
}

# Randy's schedule:
# Monday: 9:00-9:30, 11:00-12:00, 12:30-14:00, 14:30-15:00, 16:30-17:00
# Tuesday: 9:30-10:30, 11:00-11:30, 12:30-13:00, 13:30-14:30, 15:30-17:00
# Wednesday: 9:00-10:30, 11:30-12:00, 12:30-14:00, 14:30-16:30
randy_busy = {
    0: [(540, 570), (660, 720), (750, 840), (870, 900), (990, 1020)],
    1: [(570, 630), (660, 690), (750, 780), (810, 870), (930, 1020)],
    2: [(540, 630), (690, 720), (750, 840), (870, 990)]
}

# Helper function to enforce that the meeting [start, start+duration) 
# does not overlap with a busy interval [busy_start, busy_end).
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None       # Chosen day (encoded as 0: Monday, 1: Tuesday, 2: Wednesday)
meeting_start_val = None # Chosen meeting start time in minutes from midnight

# Iterate candidate days in our selected order (Tuesday then Wednesday)
for day in candidate_days:
    solver = Solver()
    # Ensure the meeting stays within the workday limits.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add constraints for Matthew's busy times on the current day.
    for (busy_start, busy_end) in matthew_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Add constraints for Randy's busy times on the current day.
    for (busy_start, busy_end) in randy_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Check possible start times minute-by-minute for the earliest valid meeting time.
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
    sh, sm = divmod(meeting_start_val, 60)
    eh, em = divmod(meeting_end_val, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
    print(f"A valid meeting time is on {day_names[meeting_day]} from {sh:02d}:{sm:02d} to {eh:02d}:{em:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")