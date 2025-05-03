from z3 import Solver, Int, Or, sat

# Meeting duration in minutes (30 minutes)
duration = 30

# Define the meeting start variable (minutes after midnight)
start = Int("start")

# Work hours: 9:00 = 540 minutes and 17:00 = 1020 minutes
WORK_START = 540
WORK_END = 1020

# Day encoding for candidate days: 0 = Monday, 1 = Tuesday, 2 = Wednesday.
candidate_days = [0, 1, 2]

# William's busy schedule (in minutes):
# Monday:
#   9:00-11:30 -> (540, 690)
#   12:00-14:30 -> (720, 870)
#   15:00-17:00 -> (900, 1020)
# Tuesday:
#   9:00-17:00 -> (540, 1020)
# Wednesday:
#   9:00-17:00 -> (540, 1020)
william_busy = {
    0: [(540, 690), (720, 870), (900, 1020)],
    1: [(540, 1020)],
    2: [(540, 1020)]
}

# Diana's preference: she does not want to meet on Monday after 13:00.
# This implies that on Monday (day 0) the meeting must finish by 13:00,
# i.e., start + duration <= 780.
def apply_diana_preference(day, solver):
    if day == 0:
        solver.add(start + duration <= 780)

# Helper function: the meeting interval [start, start+duration) must NOT overlap with a busy interval [busy_start, busy_end).
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None
meeting_start_val = None

# Iterate over candidate days in order (Monday, then Tuesday, then Wednesday)
for day in candidate_days:
    solver = Solver()
    
    # The meeting must fall completely within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Apply Diana's scheduling preference for Monday.
    apply_diana_preference(day, solver)
    
    # Add William's busy schedule constraints for the day.
    for busy_interval in william_busy.get(day, []):
        b_start, b_end = busy_interval
        solver.add(non_overlap(b_start, b_end))
    
    # Search for the earliest valid start time (minute-by-minute) on the day.
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
    start_hr, start_min = divmod(meeting_start_val, 60)
    end_hr, end_min = divmod(meeting_end_val, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
    print(f"A valid meeting time is on {day_names[meeting_day]} from {start_hr:02d}:{start_min:02d} to {end_hr:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")