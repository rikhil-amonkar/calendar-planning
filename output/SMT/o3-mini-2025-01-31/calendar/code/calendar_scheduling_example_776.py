from z3 import Solver, Int, Or, sat

# Meeting duration: 30 minutes
duration = 30

# Define the meeting start time in minutes since midnight
start = Int("start")

# Work hours: 9:00 (540 min) to 17:00 (1020 min)
WORK_START = 540
WORK_END = 1020

# Days: 0 = Monday, 1 = Tuesday, 2 = Wednesday.
# According to John's preference, he would like to avoid meetings on Monday after 14:30.
# Thus, for Monday (day == 0), we add the extra constraint that the meeting must end by 14:30 (870 min).
candidate_days = [0, 1, 2]

# John's calendar: No meetings all week.
john_busy = {
    0: [],
    1: [],
    2: []
}

# Jennifer's calendar (busy intervals in minutes):
# Monday:
#  9:00-11:00   -> (540, 660)
#  11:30-13:00  -> (690, 780)
#  13:30-14:30  -> (810, 870)
#  15:00-17:00  -> (900, 1020)
# Tuesday:
#  9:00-11:30   -> (540, 690)
#  12:00-17:00  -> (720, 1020)
# Wednesday:
#  9:00-11:30   -> (540, 690)
#  12:00-12:30  -> (720, 750)
#  13:00-14:00  -> (780, 840)
#  14:30-16:00  -> (870, 960)
#  16:30-17:00  -> (990, 1020)
jennifer_busy = {
    0: [(540, 660), (690, 780), (810, 870), (900, 1020)],
    1: [(540, 690), (720, 1020)],
    2: [(540, 690), (720, 750), (780, 840), (870, 960), (990, 1020)]
}

# Helper function: return constraint that meeting [start, start+duration) doesn't overlap a busy interval [b_start, b_end)
def non_overlap(b_start, b_end):
    return Or(start + duration <= b_start, start >= b_end)

found = False
selected_day = None
selected_start = None

# Try candidate days in the order: Monday, Tuesday, Wednesday.
for day in candidate_days:
    solver = Solver()
    # The meeting must lie within working hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # For Monday, respect John's preference: meeting must end by 14:30 (870 minutes).
    if day == 0:
        solver.add(start + duration <= 870)
    
    # Add John's constraints (none in this case).
    for b_start, b_end in john_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Add Jennifer's busy constraints.
    for b_start, b_end in jennifer_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Search for the earliest time slot minute-by-minute.
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t)
        if solver.check() == sat:
            selected_start = t
            selected_day = day
            found = True
            solver.pop()
            break
        solver.pop()
    
    if found:
        break

if found:
    selected_end = selected_start + duration
    start_hr, start_min = divmod(selected_start, 60)
    end_hr, end_min = divmod(selected_end, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
    print(f"A valid meeting time is on {day_names[selected_day]} from {start_hr:02d}:{start_min:02d} to {end_hr:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")