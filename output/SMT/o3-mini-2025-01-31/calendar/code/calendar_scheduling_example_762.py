from z3 import Solver, Int, Or, sat

# Meeting duration (in minutes)
duration = 60

# Meeting start time variable (in minutes after midnight)
start = Int("start")

# Define work hours: 9:00 to 17:00 (in minutes after midnight)
WORK_START = 540
WORK_END = 1020

# Day encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday
candidate_days = [0, 1, 2]

# Jacob's busy schedule (in minutes)
# Monday:
#   10:00 to 10:30 -> (600, 630)
#   11:00 to 11:30 -> (660, 690)
#   14:00 to 14:30 -> (840, 870)
#   15:30 to 16:00 -> (930, 960)
#   16:30 to 17:00 -> (990, 1020)
# Tuesday:
#   12:00 to 14:00 -> (720, 840)
#   15:00 to 15:30 -> (900, 930)
# Wednesday:
#   11:00 to 11:30 -> (660, 690)
#   14:30 to 15:00 -> (870, 900)
jacob_busy = {
    0: [(600, 630), (660, 690), (840, 870), (930, 960), (990, 1020)],
    1: [(720, 840), (900, 930)],
    2: [(660, 690), (870, 900)]
}

# Randy's busy schedule (in minutes)
# Monday:
#   9:00 to 9:30 -> (540, 570)
#   11:00 to 12:30 -> (660, 750)
#   13:00 to 14:00 -> (780, 840)
#   14:30 to 15:00 -> (870, 900)
#   15:30 to 17:00 -> (930, 1020)
# Tuesday:
#   9:00 to 13:30 -> (540, 810)
#   14:00 to 17:00 -> (840, 1020)
# Wednesday:
#   9:00 to 12:30 -> (540, 750)
#   14:00 to 15:00 -> (840, 900)
#   15:30 to 16:00 -> (930, 960)
#   16:30 to 17:00 -> (990, 1020)
randy_busy = {
    0: [(540, 570), (660, 750), (780, 840), (870, 900), (930, 1020)],
    1: [(540, 810), (840, 1020)],
    2: [(540, 750), (840, 900), (930, 960), (990, 1020)]
}

# Helper function:
# Ensure that the meeting interval [start, start+duration) does NOT overlap with a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    # Meeting must finish before busy_start OR start after busy_end
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None       # Stores day index
meeting_start_val = None # Meeting start time in minutes after midnight

# Iterate through each candidate day (Monday, Tuesday, Wednesday)
for day in candidate_days:
    solver = Solver()
    # Constrain meeting start and end to be within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Jacob's busy constraints for the given day.
    for busy_start, busy_end in jacob_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Add Randy's busy constraints for the given day.
    for busy_start, busy_end in randy_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Search for the earliest meeting start time on this day.
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
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
    print(f"A valid meeting time is on {day_names[meeting_day]} from {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")