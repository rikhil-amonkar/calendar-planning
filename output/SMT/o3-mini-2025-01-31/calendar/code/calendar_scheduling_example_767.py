from z3 import Solver, Int, Or, sat

# Meeting duration: 60 minutes
duration = 60

# Meeting start variable (in minutes after midnight)
start = Int("start")

# Define work hours in minutes (9:00=540, 17:00=1020)
WORK_START = 540
WORK_END = 1020

# Day encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday.
candidate_days = [0, 1, 2]

# Martha's busy schedule (in minutes):
# Monday: 16:00 to 17:00 -> (960, 1020)
# Tuesday: 15:00 to 15:30 -> (900, 930)
# Wednesday: 10:00 to 11:00 -> (600, 660); 14:00 to 14:30 -> (840, 870)
martha_busy = {
    0: [(960, 1020)],
    1: [(900, 930)],
    2: [(600, 660), (840, 870)]
}

# Beverly's busy schedule (in minutes):
# Monday: 9:00 to 13:30 -> (540, 810); 14:00 to 17:00 -> (840, 1020)
# Tuesday: 9:00 to 17:00 -> (540, 1020)
# Wednesday: 9:30 to 15:30 -> (570, 930); 16:30 to 17:00 -> (990, 1020)
beverly_busy = {
    0: [(540, 810), (840, 1020)],
    1: [(540, 1020)],
    2: [(570, 930), (990, 1020)]
}

def non_overlap(busy_start, busy_end):
    # The meeting interval [start, start+duration)
    # does NOT overlap with busy interval [busy_start, busy_end).
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None
meeting_start_val = None

# Iterate through candidate days in order (earliest availability)
for day in candidate_days:
    solver = Solver()
    # Meeting must fall completely within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Enforce Martha's busy constraints for the day.
    for b in martha_busy.get(day, []):
        b_start, b_end = b
        solver.add(non_overlap(b_start, b_end))
    
    # Enforce Beverly's busy constraints for the day.
    for b in beverly_busy.get(day, []):
        b_start, b_end = b
        solver.add(non_overlap(b_start, b_end))
    
    # Iterate minute-by-minute for the earliest valid meeting start on this day.
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