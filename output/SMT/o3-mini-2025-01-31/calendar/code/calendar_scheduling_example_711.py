from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 60  # meeting duration in minutes (one hour)
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Days encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday
days = [0, 1, 2]

# Mason's busy schedule (in minutes):
mason_busy = {
    0: [
        (9*60 + 30, 10*60),  # Monday: 9:30 to 10:00 -> (570,600)
        (10*60 + 30, 11*60)  # Monday: 10:30 to 11:00 -> (630,660)
    ],
    1: [
        (9*60 + 30, 10*60),   # Tuesday: 9:30 to 10:00 -> (570,600)
        (14*60, 14*60 + 30)   # Tuesday: 14:00 to 14:30 -> (840,870)
    ],
    2: [
        (14*60 + 30, 15*60),  # Wednesday: 14:30 to 15:00 -> (870,900)
        (15*60 + 30, 16*60)   # Wednesday: 15:30 to 16:00 -> (930,960)
    ]
}

# Nicole's busy schedule (in minutes):
nicole_busy = {
    0: [
        (WORK_START, WORK_END)  # Monday: busy entire day
    ],
    1: [
        (WORK_START, WORK_END)  # Tuesday: busy entire day
    ],
    2: [
        (9*60, 9*60 + 30),     # Wednesday: 9:00 to 9:30 -> (540,570)
        (11*60, 14*60 + 30),    # Wednesday: 11:00 to 14:30 -> (660,870)
        (15*60, 16*60)         # Wednesday: 15:00 to 16:00 -> (900,960)
    ]
}

def non_overlap(busy_start, busy_end):
    # The meeting interval [start, start+duration) should not overlap with [busy_start, busy_end)
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None  # Will be 0, 1, or 2
meeting_start = None

# We want the earliest available meeting slot overall.
# Iterate through days in order (Monday, then Tuesday, then Wednesday)
for day in days:
    solver = Solver()
    # Constrain meeting within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Mason's busy constraints for the day.
    for b_start, b_end in mason_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Add Nicole's busy constraints for the day.
    for b_start, b_end in nicole_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Search for the earliest meeting start time (minute resolution).
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