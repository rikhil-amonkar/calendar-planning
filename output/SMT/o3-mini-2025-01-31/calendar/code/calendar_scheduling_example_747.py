from z3 import Solver, Int, Or, sat

# Duration of the meeting in minutes (30 minutes)
duration = 30

# Meeting start time variable (in minutes after midnight)
start = Int("start")

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Days encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday.
# We'll try candidate days in order: Monday, Tuesday, then Wednesday.
candidate_days = [0, 1, 2]

# Megan's busy schedule (only on Wednesday)
# Wednesday: 10:00-10:30 => (600, 630), 12:00-12:30 => (720, 750)
megan_busy = {
    2: [(600, 630), (720, 750)]
}

# Jacqueline's busy schedule:
# Monday: 9:00-11:00 => (540, 660), 11:30-14:30 => (690, 870), 
#         15:00-16:00 => (900, 960), 16:30-17:00 => (990, 1020)
# Tuesday: 10:00-12:00 => (600, 720), 12:30-16:00 => (750, 960),
#          16:30-17:00 => (990, 1020)
# Wednesday: 9:00-10:00 => (540, 600), 11:00-12:00 => (660, 720), 
#            13:30-15:00 => (810, 900)
jacqueline_busy = {
    0: [(540, 660), (690, 870), (900, 960), (990, 1020)],
    1: [(600, 720), (750, 960), (990, 1020)],
    2: [(540, 600), (660, 720), (810, 900)]
}

# Helper function to ensure that a meeting [start, start+duration) does not overlap
# with a busy interval [busy_start, busy_end).
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None       # The selected day as a number (0, 1, or 2)
meeting_start_val = None # The selected meeting start time (in minutes from midnight)

# Iterate through candidate days in order to find the earliest valid meeting time.
for day in candidate_days:
    solver = Solver()
    # Constrain meeting to be within the work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Megan's busy constraints for the day (if any)
    for busy_interval in megan_busy.get(day, []):
        solver.add(non_overlap(busy_interval[0], busy_interval[1]))
    
    # Add Jacqueline's busy constraints for the day (if any)
    for busy_interval in jacqueline_busy.get(day, []):
        solver.add(non_overlap(busy_interval[0], busy_interval[1]))
    
    # Try every minute in the work day to find the earliest available start time.
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