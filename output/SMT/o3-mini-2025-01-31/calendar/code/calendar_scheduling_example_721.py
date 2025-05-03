from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 60  # meeting duration in minutes (1 hour)
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Days encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday
# Carol cannot meet on Tuesday, so allowed days are Monday and Wednesday.
allowed_days = [0, 2]

# Busy schedules for each participant (times in minutes from midnight)

# Jessica's busy schedule:
# Monday: 9:30 - 10:00, 11:30 - 12:30
# Tuesday: 9:30 - 10:00, 11:00 - 11:30, 12:00 - 14:30, 15:30 - 16:00
# Wednesday: 12:00 - 12:30, 13:30 - 14:30
jessica_busy = {
    0: [(9*60+30, 10*60), (11*60+30, 12*60+30)],
    1: [(9*60+30, 10*60), (11*60, 11*60+30), (12*60, 14*60+30), (15*60+30, 16*60)],
    2: [(12*60, 12*60+30), (13*60+30, 14*60+30)]
}

# Carol's busy schedule:
# Monday: 9:00 - 11:30, 12:00 - 13:30, 14:00 - 14:30, 15:00 - 16:30
# Tuesday: 9:30 - 10:00, 11:30 - 12:30, 14:00 - 14:30, 15:00 - 15:30, 16:00 - 16:30
# Wednesday: 9:30 - 10:30, 12:00 - 15:00, 15:30 - 16:00, 16:30 - 17:00
carol_busy = {
    0: [(9*60, 11*60+30), (12*60, 13*60+30), (14*60, 14*60+30), (15*60, 16*60+30)],
    1: [(9*60+30, 10*60), (11*60+30, 12*60+30), (14*60, 14*60+30), (15*60, 15*60+30), (16*60, 16*60+30)],
    2: [(9*60+30, 10*60+30), (12*60, 15*60), (15*60+30, 16*60), (16*60+30, 17*60)]
}

# Helper function: meeting [start, start+duration) must not overlap a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None         # will hold the day (0: Monday, 2: Wednesday)
meeting_start_val = None   # meeting start time in minutes from midnight

# Iterate over allowed days in order (earlier in the week first)
for day in allowed_days:
    solver = Solver()
    # Add constraint for meeting to be within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Jessica's busy time constraints for the given day.
    for busy_start, busy_end in jessica_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
        
    # Add Carol's busy time constraints for the given day.
    for busy_start, busy_end in carol_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Check minute-by-minute for the earliest valid start time.
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
    # Convert meeting times from minutes to HH:MM format
    start_hour, start_min = divmod(meeting_start_val, 60)
    end_hour, end_min = divmod(meeting_end_val, 60)
    day_name = {0: "Monday", 2: "Wednesday"}.get(meeting_day, "Unknown")
    print(f"A valid meeting time is on {day_name} from {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")