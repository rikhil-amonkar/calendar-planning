from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30  # meeting duration in minutes (half an hour)
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Days encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday.
# Janet prefers to avoid Wednesday meetings, so we try days in the order:
# Monday, then Tuesday, then Wednesday.
candidate_days = [0, 1, 2]

# Wayne's busy schedule (times in minutes from midnight)
wayne_busy = {
    0: [  # Monday
        (630, 660),   # 10:30 to 11:00
        (780, 840)    # 13:00 to 14:00
    ],
    1: [  # Tuesday
        (570, 600),   # 9:30 to 10:00
        (810, 840),   # 13:30 to 14:00
        (870, 900),   # 14:30 to 15:00
        (930, 960),   # 15:30 to 16:00
        (990, 1020)   # 16:30 to 17:00
    ],
    2: [  # Wednesday
        (600, 630),   # 10:00 to 10:30
        (810, 840)    # 13:30 to 14:00
    ]
}

# Janet's busy schedule (times in minutes from midnight)
janet_busy = {
    0: [  # Monday
        (540, 1020)   # busy the entire day from 9:00 to 17:00
    ],
    1: [  # Tuesday
        (540, 870),   # 9:00 to 14:30
        (900, 960),   # 15:00 to 16:00
        (990, 1020)   # 16:30 to 17:00
    ],
    2: [  # Wednesday
        (570, 900),   # 9:30 to 15:00
        (930, 1020)   # 15:30 to 17:00
    ]
}

# Helper function: ensure meeting interval [start, start + duration)
# does not overlap with a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None       # Day when meeting is scheduled (0,1,2)
meeting_start_val = None # Meeting start time in minutes from midnight

# Iterate over candidate days according to preference:
for day in candidate_days:
    solver = Solver()
    
    # Meeting must occur within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Wayne's busy constraints for the day.
    for busy_interval in wayne_busy.get(day, []):
        busy_start, busy_end = busy_interval
        solver.add(non_overlap(busy_start, busy_end))
    
    # Add Janet's busy constraints for the day.
    for busy_interval in janet_busy.get(day, []):
        busy_start, busy_end = busy_interval
        solver.add(non_overlap(busy_start, busy_end))
    
    # Try to find the earliest possible start time (minute-by-minute)
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
    day_name = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}.get(meeting_day, "Unknown")
    print(f"A valid meeting time is on {day_name} from {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")