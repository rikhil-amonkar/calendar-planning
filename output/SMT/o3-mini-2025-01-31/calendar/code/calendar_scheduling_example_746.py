from z3 import Solver, Int, Or, sat

# Duration of the meeting in minutes (60 minutes)
duration = 60

# Meeting start time variable (in minutes after midnight)
start = Int("start")

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Days encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday.
# Jeffrey does not want to meet on Monday, so we consider Tuesday and Wednesday.
candidate_days = [1, 2]

# Christine's calendar is fully open, so no busy times.

# Jeffrey's busy schedule (times expressed in minutes after midnight):
# Monday: 9:00-10:30, 11:00-12:00, 13:00-13:30, 14:00-14:30 (Not used since Jeffrey wouldn't meet on Monday)
# Tuesday: 9:00-10:00, 11:00-11:30, 13:30-15:30, 16:30-17:00
# Wednesday: 9:00-9:30, 10:00-11:30, 12:00-13:30, 14:00-15:00, 15:30-16:00, 16:30-17:00
jeffrey_busy = {
    1: [(540, 600), (660, 690), (810, 930), (990, 1020)],
    2: [(540, 570), (600, 690), (720, 810), (840, 900), (930, 960), (990, 1020)]
}

# Helper function: meeting [start, start+duration) should not overlap with a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None       # Chosen day (1: Tuesday, 2: Wednesday)
meeting_start_val = None # Chosen meeting start time (minutes after midnight)

# Check candidate days in order (Tuesday then Wednesday) for earliest available meeting.
for day in candidate_days:
    solver = Solver()
    # Ensure the meeting is entirely within the workday.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Jeffrey's busy constraints for the given day.
    for (busy_start, busy_end) in jeffrey_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Iterate over all possible start times (minute by minute) to find the earliest valid slot.
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
    sh, sm = divmod(meeting_start_val, 60)
    eh, em = divmod(meeting_end_val, 60)
    day_names = {1: "Tuesday", 2: "Wednesday"}
    print(f"A valid meeting time is on {day_names[meeting_day]} from {sh:02d}:{sm:02d} to {eh:02d}:{em:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")