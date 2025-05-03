from z3 import Solver, Int, Or, sat

# Duration of the meeting in minutes (30 minutes)
duration = 30

# Meeting start time variable (in minutes after midnight)
start = Int("start")

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Days encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday.
# Anthony cannot meet on Tuesday so we only consider Monday and Wednesday.
candidate_days = [0, 2]

# Busy schedules for each participant (times in minutes after midnight):

# Anthony's busy schedule:
# Monday: 10:00-10:30, 11:00-11:30, 12:00-12:30, 13:00-14:00
# Tuesday: 9:00-9:30, 10:00-10:30, 14:30-16:00    [Not considered due to constraint]
# Wednesday: 9:30-10:30, 13:00-13:30, 15:00-15:30
anthony_busy = {
    0: [(600, 630), (660, 690), (720, 750), (780, 840)],
    2: [(570, 630), (780, 810), (900, 930)]
}

# Gerald's busy schedule:
# Monday: 9:00-13:00, 13:30-14:30
# Tuesday: 9:30-11:30, 12:00-14:00, 14:30-17:00    [Not considered since Anthony cannot meet on Tuesday]
# Wednesday: 9:00-9:30, 10:00-17:00
gerald_busy = {
    0: [(540, 780), (810, 870)],
    2: [(540, 570), (600, 1020)]
}

# Helper function to ensure that a meeting [start, start+duration) does not overlap 
# a given busy interval [busy_start, busy_end).
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None       # Chosen day (0: Monday, 2: Wednesday)
meeting_start_val = None # Chosen meeting start time (minutes from midnight)

# Iterate candidate days in calendar order to meet the earliest availability.
for day in candidate_days:
    solver = Solver()
    # Enforce that the meeting is within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Anthony's busy constraints for the current day.
    for (busy_start, busy_end) in anthony_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Add Gerald's busy constraints for the current day.
    for (busy_start, busy_end) in gerald_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Iterate minute-by-minute to find the earliest possible start time.
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
    start_hour, start_min = divmod(meeting_start_val, 60)
    end_hour, end_min = divmod(meeting_end_val, 60)
    day_names = {0: "Monday", 2: "Wednesday"}
    print(f"A valid meeting time is on {day_names[meeting_day]} from {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")