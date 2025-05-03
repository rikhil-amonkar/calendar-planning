from z3 import Solver, Int, Or, sat

# Meeting duration (30 minutes)
duration = 30

# Meeting start variable (minutes after midnight)
start = Int("start")

# Work day hours in minutes (9:00=540, 17:00=1020)
WORK_START = 540
WORK_END = 1020

# Day encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday.
candidate_days = [0, 1, 2]

# Denise's busy schedule (in minutes):
# Monday: [13:00, 14:00) -> (780, 840); [15:30, 16:00) -> (930, 960)
# Tuesday: [12:00, 12:30) -> (720,750); [16:00, 16:30) -> (960,990)
# Wednesday: [9:30, 10:00) -> (570,600); [11:00, 11:30) -> (660,690); 
#            [13:00, 13:30) -> (780,810); [14:30, 15:30) -> (870,930)
denise_busy = {
    0: [(780, 840), (930, 960)],
    1: [(720, 750), (960, 990)],
    2: [(570, 600), (660, 690), (780, 810), (870, 930)]
}

# Keith's busy schedule (in minutes):
# Monday: [9:00, 10:30) -> (540,630); [11:30, 12:00) -> (690,720);
#         [12:30, 13:30) -> (750,810); [14:00, 14:30) -> (840,870);
#         [15:30, 17:00) -> (930,1020)
# Tuesday: [9:00, 17:00) -> (540,1020)
# Wednesday: [10:30, 11:30) -> (630,690); [12:00, 13:00) -> (720,780);
#            [13:30, 15:00) -> (810,900); [15:30, 16:00) -> (930,960)
keith_busy = {
    0: [(540,630), (690,720), (750,810), (840,870), (930,1020)],
    1: [(540,1020)],
    2: [(630,690), (720,780), (810,900), (930,960)]
}

# Denise's preference: does not want to meet on Wednesday after 11:30.
# We'll interpret it such that, on Wednesday (day=2), the meeting must finish by 11:30.
# That is: start + duration <= 690 (since 11:30 is 690 minutes after midnight).
def apply_denise_preference(day, solver):
    if day == 2:
        solver.add(start + duration <= 690)

# Keith's preference: does not want to meet on Monday.
# We enforce that by not considering Monday.
def apply_keith_preference(day, solver):
    if day == 0:
        solver.add(False)

# Helper: the meeting time interval [start, start+duration) must NOT overlap with a busy interval [busy_start, busy_end).
def non_overlap(busy_start, busy_end):
    # Non overlap if meeting ends before busy starts OR meeting starts after busy ends.
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None
meeting_start_val = None

# Iterate over candidate days in order of preference (earliest availability).
for day in candidate_days:
    solver = Solver()
    
    # Meeting must lie within the work day hours
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Apply participant preferences
    apply_keith_preference(day, solver)
    apply_denise_preference(day, solver)
    
    # Enforce Denise's busy schedule constraints for the day.
    for (b_start, b_end) in denise_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Enforce Keith's busy schedule constraints for the day.
    for (b_start, b_end) in keith_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Try to find the earliest time (minute-by-minute search).
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