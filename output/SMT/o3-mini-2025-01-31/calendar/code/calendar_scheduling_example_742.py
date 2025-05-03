from z3 import Solver, Int, Or, sat

# Duration of the meeting in minutes
duration = 30

# Meeting start time variable (in minutes after midnight)
start = Int("start")

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Days encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday.
# We want the earliest overall availability (by calendar order).
candidate_days = [0, 1, 2]

# Busy schedules for each participant, expressed in minutes from midnight.
# Philip's schedule:
# Monday: 9:00-9:30, 12:00-12:30, 13:00-14:00, 15:00-15:30, 16:00-16:30
# Tuesday: 11:30-13:00, 14:00-15:00
# Wednesday: 9:00-9:30, 10:00-10:30, 11:00-11:30, 12:30-13:00, 14:00-14:30, 15:00-15:30, 16:00-16:30
philip_busy = {
    0: [(540, 570), (720, 750), (780, 840), (900, 930), (960, 990)],
    1: [(690, 780), (840, 900)],
    2: [(540, 570), (600, 630), (660, 690), (750, 780), (840, 870), (900, 930), (960, 990)]
}

# Randy's schedule:
# Monday: 9:00-14:00, 14:30-17:00
# Tuesday: 9:00-14:00, 14:30-17:00
# Wednesday: 10:00-17:00
randy_busy = {
    0: [(540, 840), (870, 1020)],
    1: [(540, 840), (870, 1020)],
    2: [(600, 1020)]
}

# Helper function to ensure that a meeting [start, start+duration) does not overlap
# a given busy interval [busy_start, busy_end).
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None       # Chosen day (0: Monday, 1: Tuesday, 2: Wednesday)
meeting_start_val = None # Chosen meeting start time (minutes from midnight)

# Iterate candidate days in calendar order for earliest availability.
for day in candidate_days:
    solver = Solver()
    # Enforce that the meeting is within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Philip's busy constraints for the current day.
    for (busy_start, busy_end) in philip_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Add Randy's busy constraints for the current day.
    for (busy_start, busy_end) in randy_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Now, find the earliest start time on this day by iterating minute-by-minute.
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
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
    print(f"A valid meeting time is on {day_names[meeting_day]} from {sh:02d}:{sm:02d} to {eh:02d}:{em:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")