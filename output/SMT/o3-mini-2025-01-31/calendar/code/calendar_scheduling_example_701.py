from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30  # 30-minute meeting duration
start = Int("start")  # meeting start time (in minutes from midnight)

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# We represent days as: 0 = Monday, 1 = Tuesday, 2 = Wednesday

# Albert's busy schedule (in minutes):
# Monday (day 0): 9:30-10:00, 10:30-11:00, 11:30-13:00, 16:00-16:30
# Wednesday (day 2): 9:00-10:00, 15:30-16:30
albert_busy = {
    0: [(570,600), (630,660), (690,780), (960,990)],
    2: [(540,600), (930,990)]
}

# Patricia's busy schedule (in minutes):
# Monday (day 0): 9:00-17:00 (fully occupied)
# Tuesday (day 1): 9:00-14:30, 16:00-17:00
# Wednesday (day 2): 9:00-14:30, 15:00-17:00
patricia_busy = {
    0: [(540,1020)],
    1: [(540,870), (960,1020)],
    2: [(540,870), (900,1020)]
}

# Additional constraint:
# Patricia does not want to meet on Wednesday (day 2).
# So we disallow scheduling meetings on day 2.

# A helper function to enforce that the meeting interval [start, start+duration)
# does not overlap with a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None  # 0: Monday, 1: Tuesday, 2: Wednesday
meeting_start = None

# Consider days in order: Monday, Tuesday, Wednesday.
# However, note that Patricia is fully busy on Monday and does not want Wednesday.
# The solver will find a valid meeting time if one exists.
for day in [0, 1, 2]:
    solver = Solver()
    
    # Meeting must lie within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Albert's busy constraints (if any) for the given day.
    for busy_start, busy_end in albert_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Add Patricia's busy constraints (if any) for the given day.
    for busy_start, busy_end in patricia_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Enforce Patricia's preference: do not meet on Wednesday (day 2).
    if day == 2:
        solver.add(False)
    
    # Try possible start times in order (earliest first).
    lower_bound = WORK_START
    upper_bound = WORK_END - duration
    for t in range(lower_bound, upper_bound + 1):
        solver.push()
        solver.add(start == t)
        if solver.check() == sat:
            meeting_start = t
            meeting_day = day
            found = True
            solver.pop()  # remove the last constraint
            break
        solver.pop()
    
    if found:
        break

if found:
    meeting_end = meeting_start + duration
    # Convert minutes to HH:MM
    start_hour, start_min = divmod(meeting_start, 60)
    end_hour, end_min = divmod(meeting_end, 60)
    day_str = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}[meeting_day]
    print(f"A valid meeting time is on {day_str} from {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")