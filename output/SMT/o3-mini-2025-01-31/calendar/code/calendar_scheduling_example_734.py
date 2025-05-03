from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 60  # meeting duration in minutes (1 hour)
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Days encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday
# Tyler would rather not meet on Tuesday and Wednesday.
# Hence, we try candidate days in the preferred order: Monday, then Tuesday, then Wednesday.
candidate_days = [0, 1, 2]

# Nancy's busy schedule in minutes from midnight:
nancy_busy = {
    0: [  # Monday
        (600, 630),   # 10:00 to 10:30
        (750, 780),   # 12:30 to 13:00
        (810, 870)    # 13:30 to 14:30
    ],
    1: [  # Tuesday
        (630, 660),   # 10:30 to 11:00
        (690, 720),   # 11:30 to 12:00
        (750, 780)    # 12:30 to 13:00
    ],
    2: [  # Wednesday
        (570, 600),   # 9:30 to 10:00
        (690, 720),   # 11:30 to 12:00
        (840, 870),   # 14:00 to 14:30
        (960, 1020)   # 16:00 to 17:00
    ]
}

# Tyler's busy schedule in minutes from midnight:
tyler_busy = {
    0: [  # Monday
        (570, 780),   # 9:30 to 13:00
        (840, 900),   # 14:00 to 15:00
        (930, 960)    # 15:30 to 16:00
    ],
    1: [  # Tuesday
        (720, 780),   # 12:00 to 13:00
        (810, 840),   # 13:30 to 14:00
        (900, 930)    # 15:00 to 15:30
    ],
    2: [  # Wednesday
        (540, 630),   # 9:00 to 10:30
        (690, 720),   # 11:30 to 12:00
        (750, 840),   # 12:30 to 14:00
        (870, 1020)   # 14:30 to 17:00
    ]
}

# Helper function to ensure the meeting interval [start, start+duration)
# does not overlap with the busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None       # Candidate day when meeting is scheduled (0,1,2)
meeting_start_val = None # Meeting start time in minutes from midnight

# Iterate over candidate days in preferred order.
for day in candidate_days:
    solver = Solver()
    # Meeting must be scheduled within work hours:
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Nancy's busy constraints for the day.
    for busy_interval in nancy_busy.get(day, []):
        busy_start, busy_end = busy_interval
        solver.add(non_overlap(busy_start, busy_end))
    
    # Add Tyler's busy constraints for the day.
    for busy_interval in tyler_busy.get(day, []):
        busy_start, busy_end = busy_interval
        solver.add(non_overlap(busy_start, busy_end))
    
    # Try to find the earliest available meeting time in the day minute-by-minute.
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