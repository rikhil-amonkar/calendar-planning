from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30  # meeting duration in minutes (half an hour)
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END   = 1020

# Days encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday.
candidate_days = [0, 1, 2]

# Ronald's busy schedule (times in minutes from midnight)
ronald_busy = {
    0: [  # Monday
        (630, 660),   # 10:30 to 11:00
        (720, 750),   # 12:00 to 12:30
        (930, 960)    # 15:30 to 16:00
    ],
    1: [  # Tuesday
        (540, 570),   # 9:00 to 9:30
        (720, 750),   # 12:00 to 12:30
        (930, 990)    # 15:30 to 16:30
    ],
    2: [  # Wednesday
        (570, 630),   # 9:30 to 10:30
        (660, 720),   # 11:00 to 12:00
        (750, 780),   # 12:30 to 13:00
        (810, 840),   # 13:30 to 14:00
        (990, 1020)   # 16:30 to 17:00
    ]
}

# Amber's busy schedule (times in minutes from midnight)
amber_busy = {
    0: [  # Monday
        (540, 570),   # 9:00 to 9:30
        (600, 630),   # 10:00 to 10:30
        (690, 720),   # 11:30 to 12:00
        (750, 840),   # 12:30 to 14:00
        (870, 900),   # 14:30 to 15:00
        (930, 1020)   # 15:30 to 17:00
    ],
    1: [  # Tuesday
        (540, 570),   # 9:00 to 9:30
        (600, 690),   # 10:00 to 11:30
        (720, 750),   # 12:00 to 12:30
        (810, 930),   # 13:30 to 15:30
        (990, 1020)   # 16:30 to 17:00
    ],
    2: [  # Wednesday
        (540, 570),   # 9:00 to 9:30
        (600, 630),   # 10:00 to 10:30
        (660, 810),   # 11:00 to 13:30
        (900, 930)    # 15:00 to 15:30
    ]
}

# Helper function to ensure meeting interval [start, start+duration)
# does not overlap with busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None       # Day when meeting is scheduled (0,1,2)
meeting_start_val = None # Meeting start time (minutes from midnight)

# Try candidate days in order, looking for the earliest available slot.
for day in candidate_days:
    solver = Solver()
    
    # Ensure meeting is within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Ronald's busy time constraints for the day.
    for busy_interval in ronald_busy.get(day, []):
        busy_start, busy_end = busy_interval
        solver.add(non_overlap(busy_start, busy_end))
        
    # Add Amber's busy time constraints for the day.
    for busy_interval in amber_busy.get(day, []):
        busy_start, busy_end = busy_interval
        solver.add(non_overlap(busy_start, busy_end))
    
    # Look for the earliest meeting start time by iterating minute-by-minute.
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