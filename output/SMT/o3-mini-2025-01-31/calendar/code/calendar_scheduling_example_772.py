from z3 import Solver, Int, Or, sat

# Meeting duration: 30 minutes
duration = 30

# The meeting start time (minutes from midnight)
start = Int("start")

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Day encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday.
candidate_days = [0, 1, 2]

# Walter's busy schedule (in minutes):
# Monday: 9:30 to 10:00 -> (570,600)
# Tuesday: 10:00 to 10:30 -> (600,630), 12:00 to 12:30 -> (720,750)
# Wednesday: 10:00 to 10:30 -> (600,630)
walter_busy = {
    0: [(570, 600)],
    1: [(600, 630), (720, 750)],
    2: [(600, 630)]
}

# Eugene's busy schedule (in minutes):
# Monday: 9:30 to 13:30 -> (570,810), 14:00 to 17:00 -> (840,1020)
# Tuesday: 9:00 to 17:00 -> (540,1020)
# Wednesday: 9:00 to 10:30 -> (540,630), 11:00 to 16:30 -> (660,990)
eugene_busy = {
    0: [(570, 810), (840, 1020)],
    1: [(540, 1020)],
    2: [(540, 630), (660, 990)]
}

# Walter's preference:
# Walter would like to avoid more meetings on Monday before 12:00.
# So if the meeting is on Monday (day 0), then meeting must not start before 12:00 (720 minutes).
def apply_walter_preference(day, solver):
    if day == 0:
        solver.add(start >= 720)

# Helper: Non-overlap condition for a meeting interval [start, start + duration)
# and a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
selected_day = None
selected_start = None

# Iterate over candidate days (Monday, Tuesday, then Wednesday)
for day in candidate_days:
    solver = Solver()
    
    # The meeting must entirely lie within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Apply Walter's scheduling preference.
    apply_walter_preference(day, solver)
    
    # Add Walter's busy constraints for this day.
    for b_start, b_end in walter_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Add Eugene's busy constraints for this day.
    for b_start, b_end in eugene_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Search for a valid meeting start time minute-by-minute within working hours.
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