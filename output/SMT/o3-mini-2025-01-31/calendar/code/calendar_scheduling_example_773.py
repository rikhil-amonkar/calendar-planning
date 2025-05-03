from z3 import Solver, Int, Or, sat

# Meeting duration: 60 minutes
duration = 60

# Define the meeting start time (in minutes from midnight)
start = Int("start")

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Day encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday.
candidate_days = [0, 1, 2]

# Patrick's calendar is wide open, so no busy times for him.

# Roy's busy schedule (expressed in minutes):
# Monday: 10:00-11:30 -> (600,690), 12:00-13:00 -> (720,780),
#         14:00-14:30 -> (840,870), 15:00-17:00 -> (900,1020)
# Tuesday: 10:30-11:30 -> (630,690), 12:00-14:30 -> (720,870),
#          15:00-15:30 -> (900,930), 16:00-17:00 -> (960,1020)
# Wednesday: 9:30-11:30 -> (570,690), 12:30-14:00 -> (750,840),
#            14:30-15:30 -> (870,930), 16:30-17:00 -> (990,1020)
roy_busy = {
    0: [(600, 690), (720, 780), (840, 870), (900, 1020)],
    1: [(630, 690), (720, 870), (900, 930), (960, 1020)],
    2: [(570, 690), (750, 840), (870, 930), (990, 1020)]
}

# The group would like to meet at their earliest availability.
# We'll iterate candidate days in order (Monday, then Tuesday, then Wednesday),
# and within each day we'll search for the earliest start time available.

# Helper: The meeting interval [start, start+duration) must not overlap with a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
selected_day = None
selected_start = None

# Process candidate days in order: Monday (0), Tuesday (1), Wednesday (2)
for day in candidate_days:
    solver = Solver()
    
    # The meeting must lie within working hours
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # No constraints from Patrick as his calendar is free

    # Add Roy's busy constraints for this day.
    for b_start, b_end in roy_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Iterate through possible start times minute-by-minute
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t)
        if solver.check() == sat:
            selected_start = t
            selected_day = day
            found = True
            solver.pop()  # remove the push frame before breaking
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