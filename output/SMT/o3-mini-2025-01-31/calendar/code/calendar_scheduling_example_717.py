from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30  # meeting duration in minutes
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Days encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday
# Allowed days are Monday, Tuesday, Wednesday.
allowed_days = [0, 1, 2]

# Busy schedules for each participant (times in minutes from midnight)

# Evelyn's busy schedule:
# Monday: 9:00-10:00, 11:00-11:30, 12:30-14:30, 15:00-15:30, 16:00-17:00
# Tuesday: 9:30-10:00, 12:30-13:00, 14:00-15:00, 15:30-16:00
# Wednesday: 9:00-9:30, 11:30-12:00, 14:00-14:30
evelyn_busy = {
    0: [(9*60, 10*60), (11*60, 11*60+30), (12*60+30, 14*60+30), (15*60, 15*60+30), (16*60, 17*60)],
    1: [(9*60+30, 10*60), (12*60+30, 13*60), (14*60, 15*60), (15*60+30, 16*60)],
    2: [(9*60, 9*60+30), (11*60+30, 12*60), (14*60, 14*60+30)]
}

# Julia's busy schedule:
# Monday: 9:00-10:00, 10:30-15:00, 15:30-17:00
# Tuesday: 9:00-15:30, 16:00-17:00
# Wednesday: 9:00-13:00, 13:30-17:00
julia_busy = {
    0: [(9*60, 10*60), (10*60+30, 15*60), (15*60+30, 17*60)],
    1: [(9*60, 15*60+30), (16*60, 17*60)],
    2: [(9*60, 13*60), (13*60+30, 17*60)]
}

# Helper function: the meeting interval [start, start+duration) must not overlap
# with a busy interval [busy_start, busy_end).
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None         # to store the day of the meeting (0, 1, or 2)
meeting_start_val = None   # to store the meeting start time in minutes from midnight

# Try each allowed day in order (earlier day considered first)
for day in allowed_days:
    solver = Solver()
    # The meeting must occur within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add constraints for Evelyn's busy times for the given day.
    for (busy_start, busy_end) in evelyn_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Add constraints for Julia's busy times for the given day.
    for (busy_start, busy_end) in julia_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Search minute by minute for the earliest valid start time.
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
    # Convert minutes into HH:MM format.
    start_hour, start_min = divmod(meeting_start_val, 60)
    end_hour, end_min = divmod(meeting_end_val, 60)
    day_name = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}.get(meeting_day, "Unknown")
    print(f"A valid meeting time is on {day_name} from {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")