from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30  # meeting duration in minutes (half an hour)
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Days encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday
# Arthur cannot meet on Tuesday, so allowed days are Monday and Wednesday.
allowed_days = [0, 2]

# Busy schedules for each participant (times represented in minutes from midnight)

# Arthur's busy schedule:
# Monday:    11:00 to 11:30, 13:30 to 14:00, 15:00 to 15:30
# Tuesday:   13:00 to 13:30, 16:00 to 16:30       (not allowed)
# Wednesday: 10:00 to 10:30, 11:00 to 11:30, 12:00 to 12:30, 14:00 to 14:30, 16:00 to 16:30
arthur_busy = {
    0: [(11*60, 11*60+30), (13*60+30, 14*60), (15*60, 15*60+30)],
    1: [(13*60, 13*60+30), (16*60, 16*60+30)],  # Tuesday (won't be used since Arthur can't meet on Tuesday)
    2: [(10*60, 10*60+30), (11*60, 11*60+30), (12*60, 12*60+30), (14*60, 14*60+30), (16*60, 16*60+30)]
}

# Michael's busy schedule:
# Monday:    9:00 to 12:00, 12:30 to 13:00, 14:00 to 14:30, 15:00 to 17:00
# Tuesday:   9:30 to 11:30, 12:00 to 13:30, 14:00 to 15:30
# Wednesday: 10:00 to 12:30, 13:00 to 13:30
michael_busy = {
    0: [(9*60, 12*60), (12*60+30, 13*60), (14*60, 14*60+30), (15*60, 17*60)],
    1: [(9*60+30, 11*60+30), (12*60, 13*60+30), (14*60, 15*60+30)],
    2: [(10*60, 12*60+30), (13*60, 13*60+30)]
}

# Helper function: meeting interval [start, start+duration) must not overlap with a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None       # will hold the day (0: Monday, 2: Wednesday) where the meeting is scheduled
meeting_start_val = None # meeting start time in minutes from midnight

# Try each allowed day in order (earlier day first)
for day in allowed_days:
    solver = Solver()
    # The meeting must be scheduled entirely within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Arthur's non-overlap constraints for the current day.
    for busy_start, busy_end in arthur_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Add Michael's non-overlap constraints for the current day.
    for busy_start, busy_end in michael_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Find earliest possible start time by iterating minute-by-minute.
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
    # Convert time in minutes to HH:MM format.
    start_hour, start_min = divmod(meeting_start_val, 60)
    end_hour, end_min = divmod(meeting_end_val, 60)
    day_name = {0: "Monday", 2: "Wednesday"}.get(meeting_day, "Unknown")
    print(f"A valid meeting time is on {day_name} from {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")