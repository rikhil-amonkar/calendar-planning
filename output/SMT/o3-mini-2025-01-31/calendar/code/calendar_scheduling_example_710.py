from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30  # meeting duration in minutes (half an hour)
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Days encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday
# Cheryl cannot meet on Wednesday, so eligible days are Monday and Tuesday.
eligible_days = [0, 1]

# Cheryl's busy schedule (in minutes):
cheryl_busy = {
    0: [(540, 570),      # Monday: 9:00 to 9:30
        (11*60 + 30, 13*60),  # Monday: 11:30 to 13:00 -> (690, 780)
        (15*60 + 30, 16*60)], # Monday: 15:30 to 16:00 -> (930, 960)
    1: [(15*60, 15*60 + 30)]  # Tuesday: 15:00 to 15:30 -> (900, 930)
    # No schedule for Wednesday as Cheryl cannot meet on Wednesday.
}

# Kyle's busy schedule (in minutes):
kyle_busy = {
    0: [(540, 1020)],   # Monday: busy 9:00 to 17:00
    1: [(570, 1020)],   # Tuesday: busy 9:30 to 17:00
    2: [(540, 570),      # Wednesday: 9:00 to 9:30
        (600, 780),      # Wednesday: 10:00 to 13:00
        (13*60+30, 14*60),  # Wednesday: 13:30 to 14:00 -> (810,840)
        (14*60+30, 1020)]   # Wednesday: 14:30 to 17:00 -> (870,1020)
}

def non_overlap(busy_start, busy_end):
    # The meeting interval [start, start+duration) should not overlap with [busy_start, busy_end)
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None  # 0 for Monday or 1 for Tuesday
meeting_start = None

# Try each eligible day in order.
for day in eligible_days:
    solver = Solver()
    # Meeting must occur within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Cheryl's busy time constraints.
    for b_start, b_end in cheryl_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Add Kyle's busy time constraints.
    for b_start, b_end in kyle_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Try possible start times within work hours.
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t)
        if solver.check() == sat:
            meeting_start = t
            meeting_day = day
            found = True
            solver.pop()
            break
        solver.pop()
        
    if found:
        break

if found:
    meeting_end = meeting_start + duration
    # Convert minutes to HH:MM format.
    start_hour, start_min = divmod(meeting_start, 60)
    end_hour, end_min = divmod(meeting_end, 60)
    day_str = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}[meeting_day]
    print(f"A valid meeting time is on {day_str} from {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")