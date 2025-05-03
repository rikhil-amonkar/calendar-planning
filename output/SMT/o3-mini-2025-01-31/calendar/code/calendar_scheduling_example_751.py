from z3 import Solver, Int, Or, sat

# Meeting duration in minutes (30 minutes)
duration = 30

# Meeting start time variable (in minutes after midnight)
start = Int("start")

# Work hours in minutes: from 9:00 (540) to 17:00 (1020)
WORK_START = 540
WORK_END = 1020

# Days encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday.
# Edward does not want to meet on Monday or Wednesday.
# Thus, only Tuesday (day 1) is acceptable.
candidate_days = [1]

# Busy schedules in minutes

# Edward's busy schedule:
# Tuesday: 10:00 to 11:00 -> (600, 660), and 15:00 to 15:30 -> (900, 930)
edward_busy = {
    1: [(600, 660), (900, 930)]
}

# Charlotte's busy schedule:
# Tuesday: 9:00 to 11:00 -> (540, 660), 11:30 to 15:30 -> (690, 930), 16:00 to 17:00 -> (960, 1020)
charlotte_busy = {
    1: [(540, 660), (690, 930), (960, 1020)]
}

# Helper function: ensures the meeting [start, start+duration) does not overlap with a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None       # chosen candidate day
meeting_start_val = None # meeting start time in minutes after midnight

# Iterate over candidate days (only Tuesday in this case)
for day in candidate_days:
    solver = Solver()
    # Meeting must be within the work day
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Edward's busy constraints for day (Tuesday)
    for busy_start, busy_end in edward_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Add Charlotte's busy constraints for day (Tuesday)
    for busy_start, busy_end in charlotte_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Find the earliest valid meeting time by checking each minute from WORK_START onward.
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