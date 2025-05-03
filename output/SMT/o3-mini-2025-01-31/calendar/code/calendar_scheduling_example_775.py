from z3 import Solver, Int, Or, sat

# Meeting duration: 60 minutes
duration = 60

# The meeting start time (in minutes from midnight)
start = Int("start")

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Days: 0 = Monday, 1 = Tuesday, 2 = Wednesday.
# We will try candidate days in order: Monday is best (neither participant objects),
# then Tuesday (Kathryn would like to avoid Tuesday),
# then Wednesday (Denise would rather not meet on Wednesday).
candidate_days = [0, 1, 2]

# Kathryn's blocked times (in minutes):
# Monday: 11:00 to 11:30 -> (660, 690)
# Tuesday: 16:30 to 17:00 -> (990, 1020)
# Wednesday: 12:30 to 13:00 -> (750, 780), 13:30 to 14:00 -> (810, 840)
kathryn_busy = {
    0: [(660, 690)],
    1: [(990, 1020)],
    2: [(750, 780), (810, 840)]
}

# Denise's blocked times (in minutes):
# Monday: 9:30 to 13:00 -> (570, 780), 13:30 to 14:30 -> (810, 870), 16:30 to 17:00 -> (990, 1020)
# Tuesday: 9:00 to 9:30 -> (540, 570), 10:00 to 12:00 -> (600, 720), 12:30 to 13:00 -> (750, 780),
#          14:00 to 15:30 -> (840, 930), 16:30 to 17:00 -> (990, 1020)
# Wednesday: 12:00 to 12:30 -> (720, 750), 13:00 to 13:30 -> (780, 810), 16:00 to 17:00 -> (960, 1020)
denise_busy = {
    0: [(570, 780), (810, 870), (990, 1020)],
    1: [(540, 570), (600, 720), (750, 780), (840, 930), (990, 1020)],
    2: [(720, 750), (780, 810), (960, 1020)]
}

# Helper: The meeting interval [start, start+duration) must not overlap with a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
selected_day = None
selected_start = None

# Try candidate days in order
for day in candidate_days:
    solver = Solver()
    
    # The meeting must fit within working hours
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Kathryn's busy constraints for the day
    for b_start, b_end in kathryn_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Add Denise's busy constraints for the day
    for b_start, b_end in denise_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Note on preferences:
    # Kathryn would like to avoid Tuesday. Denise would rather not meet on Wednesday.
    # We honor these preferences by trying Monday first; if a solution is found on Monday,
    # we pick it immediately rather than exploring Tuesday or Wednesday.
    
    # Check for the earliest available start time (minute-by-minute)
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t)
        if solver.check() == sat:
            selected_start = t
            selected_day = day
            found = True
            solver.pop()  # Remove the temporary constraint
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