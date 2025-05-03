from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 60  # meeting duration in minutes (one hour)
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Days: 0 = Monday, 1 = Tuesday, 2 = Wednesday
# Jerry cannot meet on Monday so only Tuesday and Wednesday are considered.
days_to_consider = [1, 2]

# Henry's busy schedule (in minutes from midnight):
henry_busy = {
    0: [(11*60, 11*60 + 30),   # Monday: 11:00 to 11:30
        (12*60, 12*60 + 30),   # Monday: 12:00 to 12:30
        (16*60 + 30, 17*60)],  # Monday: 16:30 to 17:00
    1: [(9*60 + 30, 10*60),    # Tuesday: 9:30 to 10:00
        (10*60 + 30, 11*60),   # Tuesday: 10:30 to 11:00
        (11*60 + 30, 12*60),   # Tuesday: 11:30 to 12:00
        (14*60, 14*60 + 30),   # Tuesday: 14:00 to 14:30
        (16*60, 16*60 + 30)],  # Tuesday: 16:00 to 16:30
    2: [(11*60 + 30, 12*60),   # Wednesday: 11:30 to 12:00
        (12*60 + 30, 13*60),   # Wednesday: 12:30 to 13:00
        (13*60 + 30, 14*60),   # Wednesday: 13:30 to 14:00
        (16*60, 16*60 + 30)]   # Wednesday: 16:00 to 16:30
}

# Jerry's busy schedule (in minutes from midnight):
jerry_busy = {
    0: [(9*60, 11*60 + 30),    # Monday: 9:00 to 11:30
        (12*60, 12*60 + 30),   # Monday: 12:00 to 12:30
        (13*60 + 30, 15*60 + 30),  # Monday: 13:30 to 15:30
        (16*60 + 30, 17*60)],  # Monday: 16:30 to 17:00
    1: [(9*60, 9*60 + 30),     # Tuesday: 9:00 to 9:30
        (11*60, 11*60 + 30),   # Tuesday: 11:00 to 11:30
        (12*60 + 30, 14*60),   # Tuesday: 12:30 to 14:00
        (14*60 + 30, 15*60),   # Tuesday: 14:30 to 15:00
        (16*60, 17*60)],      # Tuesday: 16:00 to 17:00
    2: [(9*60, 10*60),        # Wednesday: 9:00 to 10:00
        (10*60 + 30, 12*60),   # Wednesday: 10:30 to 12:00
        (12*60 + 30, 14*60 + 30),  # Wednesday: 12:30 to 14:30
        (15*60, 17*60)]       # Wednesday: 15:00 to 17:00
}

def non_overlap(busy_start, busy_end):
    # The meeting interval [start, start+duration) must not overlap with [busy_start, busy_end)
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None  # This will be 1 (Tuesday) or 2 (Wednesday)
meeting_start = None

# Try each eligible day in order (Tuesday then Wednesday)
for day in days_to_consider:
    solver = Solver()
    # Meeting must be scheduled within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
  
    # Add Henry's busy constraints for the day.
    for b_start, b_end in henry_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Add Jerry's busy constraints for the day.
    for b_start, b_end in jerry_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Iterate over possible meeting start times (in minutes)
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