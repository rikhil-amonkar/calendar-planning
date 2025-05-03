from z3 import Solver, Int, Or, sat

# Meeting duration: 30 minutes
duration = 30

# Define meeting start time variable in minutes from midnight.
start = Int("start")

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Define days: 0 = Monday, 1 = Tuesday, 2 = Wednesday.
# Constraint: Lori cannot meet on Monday, so we only consider Tuesday and Wednesday.
candidate_days = [1, 2]  # 1: Tuesday, 2: Wednesday

# Logan's busy schedule (in minutes):
# Monday: 14:30-15:00 -> (870, 900), 15:30-16:00 -> (930, 960)
# Tuesday: 11:30-12:00 -> (690, 720)
# Wednesday: 16:00-16:30 -> (960, 990)
logan_busy = {
    0: [(870, 900), (930, 960)],
    1: [(690, 720)],
    2: [(960, 990)]
}

# Lori's busy schedule (in minutes):
# Monday: 9:00-11:30 -> (540, 690), 12:00-13:00 -> (720, 780),
#         13:30-14:30 -> (810, 870), 15:00-15:30 -> (900, 930), 16:00-17:00 -> (960, 1020)
# Tuesday: 9:00-13:00 -> (540, 780), 13:30-14:30 -> (810, 870), 15:00-17:00 -> (900, 1020)
# Wednesday: 9:00-12:30 -> (540, 750), 14:00-15:00 -> (840, 900), 15:30-17:00 -> (930, 1020)
lori_busy = {
    0: [(540, 690), (720, 780), (810, 870), (900, 930), (960, 1020)],
    1: [(540, 780), (810, 870), (900, 1020)],
    2: [(540, 750), (840, 900), (930, 1020)]
}

# Helper function for non-overlap: the meeting [start, start+duration) should not overlap [b_start, b_end)
def non_overlap(b_start, b_end):
    return Or(start + duration <= b_start, start >= b_end)

found = False
selected_day = None
selected_start = None

# Try each candidate day in order (Tuesday then Wednesday)
for day in candidate_days:
    solver = Solver()
    # Ensure meeting is within working hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Logan's busy schedules for the day.
    for b_start, b_end in logan_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Add Lori's busy schedules for the day.
    for b_start, b_end in lori_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Search minute-by-minute for the earliest available slot.
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t)
        if solver.check() == sat:
            selected_start = t
            selected_day = day
            found = True
            solver.pop()  # remove temporary constraint before breaking
            break
        solver.pop()
    
    if found:
        break

if found:
    selected_end = selected_start + duration
    start_hr, start_min = divmod(selected_start, 60)
    end_hr, end_min = divmod(selected_end, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}.".format(
        day_names[selected_day], start_hr, start_min, end_hr, end_min))
else:
    print("No valid meeting time could be found that meets all constraints.")