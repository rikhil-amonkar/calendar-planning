from z3 import Solver, Int, Or, sat

# Meeting duration: 60 minutes
duration = 60

# Define the meeting start time in minutes after midnight
start = Int("start")

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Candidate days: 0 = Monday, 1 = Tuesday, 2 = Wednesday.
candidate_days = [0, 1, 2]

# Diana's busy schedule (in minutes):
# Monday: 14:30 to 15:00 -> (870, 900), 15:30 to 16:00 -> (930, 960)
# Tuesday: 13:00 to 13:30 -> (780, 810)
# Wednesday: 9:30 to 10:00 -> (570, 600), 12:00 to 13:00 -> (720, 780),
#            14:00 to 14:30 -> (840, 870), 16:00 to 16:30 -> (960, 990)
diana_busy = {
    0: [(870, 900), (930, 960)],
    1: [(780, 810)],
    2: [(570, 600), (720, 780), (840, 870), (960, 990)]
}

# Rachel's busy schedule (in minutes):
# Monday: 9:30 to 11:30 -> (570, 690), 12:00 to 14:30 -> (720, 870), 15:00 to 17:00 -> (900, 1020)
# Tuesday: 9:30 to 12:30 -> (570, 750), 13:30 to 14:00 -> (810, 840), 16:00 to 17:00 -> (960, 1020)
# Wednesday: 10:00 to 12:30 -> (600, 750), 13:30 to 14:30 -> (810, 870), 16:30 to 17:00 -> (990, 1020)
rachel_busy = {
    0: [(570, 690), (720, 870), (900, 1020)],
    1: [(570, 750), (810, 840), (960, 1020)],
    2: [(600, 750), (810, 870), (990, 1020)]
}

# The group prefers to schedule the meeting at their earliest availability.
# That is, we now iterate over candidate days in order (Monday, then Tuesday, then Wednesday)
# and for each day we search for the earliest start time that satisfies all constraints.

# Helper function: meeting [start, start+duration) must not overlap with a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
selected_day = None
selected_start = None

# Process candidate days in order: Monday (0), Tuesday (1), Wednesday (2)
for day in candidate_days:
    solver = Solver()
    
    # The meeting must lie within working hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Diana's busy constraints for the day.
    for b_start, b_end in diana_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Add Rachel's busy constraints for the day.
    for b_start, b_end in rachel_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Iterate minute-by-minute from WORK_START to the latest possible start time.
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t)
        if solver.check() == sat:
            selected_start = t
            selected_day = day
            found = True
            solver.pop()  # Pop the temporary constraint.
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