from z3 import Solver, Int, Or, sat

# Meeting duration in minutes (30 minutes)
duration = 30

# The meeting start time variable (in minutes after midnight)
start = Int("start")

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Days encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday.
# Jason would rather not meet on Wednesday and Monday is fully busy for Jason,
# so we prioritize Tuesday and only consider Wednesday if necessary.
candidate_days = [1, 2]

# Kathryn's busy schedule (in minutes)
# Monday: 14:00-14:30 -> (840, 870)
# Tuesday: 16:00-16:30 -> (960, 990)
# Wednesday: 9:00-10:00 -> (540, 600), 12:00-12:30 -> (720, 750),
#            13:00-14:00 -> (780, 840), 16:30-17:00 -> (990, 1020)
kathryn_busy = {
    0: [(840, 870)],
    1: [(960, 990)],
    2: [(540,600), (720,750), (780,840), (990,1020)]
}

# Jason's busy schedule (in minutes)
# Monday: 9:00-17:00 -> (540, 1020)
# Tuesday: 9:30-10:30 -> (570,630), 11:00-12:00 -> (660,720), 
#          12:30-17:00 -> (750,1020)
# Wednesday: 10:00-10:30 -> (600,630), 11:00-12:00 -> (660,720), 
#            13:00-13:30 -> (780,810), 14:30-16:00 -> (870,960)
jason_busy = {
    0: [(540,1020)],
    1: [(570,630), (660,720), (750,1020)],
    2: [(600,630), (660,720), (780,810), (870,960)]
}

# Helper function:
# Ensures that the meeting [start, start+duration) does not overlap 
# with a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None       # day index (0, 1, or 2)
meeting_start_val = None # meeting start time in minutes after midnight

for day in candidate_days:
    solver = Solver()
    # Ensure meeting is scheduled within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Kathryn's busy time constraints for the day.
    for busy_start, busy_end in kathryn_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
        
    # Add Jason's busy time constraints for the day.
    for busy_start, busy_end in jason_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Since the group would like to meet at the earliest availability,
    # we try every potential starting time from WORK_START onward.
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t)
        if solver.check() == sat:
            meeting_start_val = t
            meeting_day = day
            found = True
            solver.pop()  # remove the temporary assignment
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