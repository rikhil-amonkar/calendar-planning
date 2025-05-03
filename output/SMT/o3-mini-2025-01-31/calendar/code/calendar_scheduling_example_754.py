from z3 import Solver, Int, Or, sat

# Meeting duration in minutes (30 minutes)
duration = 30

# Meeting start time variable (in minutes after midnight)
start = Int("start")

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Days encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday.
# Because Dylan does not want to meet on Wednesday, we only consider Monday and Tuesday.
candidate_days = [0, 1]

# Busy schedules in minutes

# Natalie's busy schedule:
# Monday: 9:00-9:30 -> (540,570), 14:30-17:00 -> (870,1020)
# Tuesday: 9:30-10:30 -> (570,630), 12:00-13:00 -> (720,780), 14:00-17:00 -> (840,1020)
# Wednesday: 15:30-16:30 -> (930,990)  [Not considered due to Dylan's constraint]
natalie_busy = {
    0: [(540, 570), (870, 1020)],
    1: [(570, 630), (720, 780), (840, 1020)],
    2: [(930, 990)]
}

# Dylan's busy schedule:
# Monday: 9:00-11:30 -> (540,690), 12:00-17:00 -> (720,1020)
# Tuesday: 9:00-17:00 -> (540,1020)
# Wednesday: 9:00-14:30 -> (540,870), 15:00-17:00 -> (900,1020)  [Not considered because Dylan does not want Wednesday]
dylan_busy = {
    0: [(540, 690), (720, 1020)],
    1: [(540, 1020)],
    2: [(540, 870), (900, 1020)]
}

# Helper function: the meeting [start, start+duration) must not overlap a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

# Search for a meeting time that satisfies all constraints
found = False
meeting_day = None       # day index (0, 1, or 2)
meeting_start_val = None # meeting start time in minutes after midnight

# Check candidate days in order (Monday, then Tuesday)
for day in candidate_days:
    solver = Solver()
    # Ensure the meeting is within work hours
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Natalie constraints for this day
    for busy_start, busy_end in natalie_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Add Dylan constraints for this day
    for busy_start, busy_end in dylan_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Check each possible start time from WORK_START to WORK_END - duration for the earliest valid time
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