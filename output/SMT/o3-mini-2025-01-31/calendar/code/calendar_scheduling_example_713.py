from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30  # meeting duration in minutes (half an hour)
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Days encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday
# According to constraints, Martha cannot meet on Tuesday or Wednesday,
# so we only consider Monday.
allowed_days = [0]

# Martha's busy schedule (in minutes):
martha_busy = {
    0: [ (11 * 60 + 30, 12 * 60) ],  # Monday: 11:30 to 12:00 -> (690,720)
    1: [ (13 * 60 + 30, 14 * 60), (14 * 60 + 30, 15 * 60) ],  # Tuesday (not allowed)
    2: [ (9 * 60, 9 * 60 + 30) ]  # Wednesday (not allowed)
}

# Carol's busy schedule (in minutes):
carol_busy = {
    0: [ (9 * 60 + 30, 12 * 60),      # Monday: 9:30 to 12:00 -> (570,720)
         (12 * 60 + 30, 13 * 60),     # Monday: 12:30 to 13:00 -> (750,780)
         (13 * 60 + 30, 15 * 60),     # Monday: 13:30 to 15:00 -> (810,900)
         (15 * 60 + 30, 17 * 60) ],   # Monday: 15:30 to 17:00 -> (930,1020)
    1: [ (9 * 60, 9 * 60 + 30),       # Tuesday: 9:00 to 9:30 -> (540,570)
         (12 * 60 + 30, 13 * 60),     # Tuesday: 12:30 to 13:00 -> (750,780)
         (15 * 60, 15 * 60 + 30),     # Tuesday: 15:00 to 15:30 -> (900,930)
         (16 * 60 + 30, 17 * 60) ],   # Tuesday: 16:30 to 17:00 -> (990,1020)
    2: [ (9 * 60, 9 * 60 + 30),       # Wednesday: 9:00 to 9:30 -> (540,570)
         (10 * 60, 10 * 60 + 30),     # Wednesday: 10:00 to 10:30 -> (600,630)
         (11 * 60, 11 * 60 + 30),     # Wednesday: 11:00 to 11:30 -> (660,690)
         (12 * 60, 14 * 60 + 30),     # Wednesday: 12:00 to 14:30 -> (720,870)
         (15 * 60 + 30, 16 * 60 + 30) ]  # Wednesday: 15:30 to 16:30 -> (930,990)
}

# Helper function: The meeting interval [start, start+duration) must not overlap with a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None  # 0 corresponds to Monday
meeting_start = None  # in minutes from midnight

# We are to schedule at the earliest availability.
# Since Martha can only meet on Monday, we consider day=0.
for day in allowed_days:
    solver = Solver()
    # Meeting must be within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Martha's busy time constraints (for the day).
    for busy_interval in martha_busy.get(day, []):
        b_start, b_end = busy_interval
        solver.add(non_overlap(b_start, b_end))
    
    # Add Carol's busy time constraints (for the day).
    for busy_interval in carol_busy.get(day, []):
        b_start, b_end = busy_interval
        solver.add(non_overlap(b_start, b_end))
    
    # Check minute-by-minute from WORK_START to latest possible start, 
    # so that we choose the earliest available meeting slot.
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
    day_name = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}[meeting_day]
    print(f"A valid meeting time is on {day_name} from {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found.")