from z3 import Solver, Int, Or, sat

# Meeting duration: 30 minutes
duration = 30
# Meeting start time variable (in minutes from midnight)
start = Int("start")

# Define work hours in minutes from midnight
WORK_START = 540   # 9:00
WORK_END = 1020    # 17:00

# Days encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday.
# Dorothy prefers to avoid Monday, so we try Wednesday first.
candidate_days = [2, 0]

# Busy schedules (times in minutes from midnight)

# Willie's busy schedule:
willie_busy = {
    0: [  # Monday: 15:00 to 15:30
        (900, 930)
    ],
    2: [  # Wednesday: 9:00 to 9:30
        (540, 570)
    ]
}
# If a day is not specified (like Tuesday), Willie is free.

# Dorothy's busy schedule:
dorothy_busy = {
    0: [  # Monday:
        (540, 570),   # 9:00 - 9:30
        (660, 720),   # 11:00 - 12:00
        (750, 900),   # 12:30 - 15:00
        (930, 1020)   # 15:30 - 17:00
    ],
    1: [  # Tuesday: fully booked from 9:00 to 17:00
        (540, 1020)
    ],
    2: [  # Wednesday:
        (540, 960),   # 9:00 - 16:00
        (990, 1020)   # 16:30 - 17:00
    ]
}

# Helper function: A meeting [start, start+duration) and a busy interval [busy_start, busy_end)
# must not overlap. That is, meeting must either end by busy_start or start after busy_end.
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None       # chosen day: 0 (Monday) or 2 (Wednesday)
meeting_start_val = None # meeting start time (in minutes from midnight)

# Iterate over candidate days in the preferred order.
for day in candidate_days:
    # Skip Tuesday if present; in our candidate_days only 2 and 0 appear.
    solver = Solver()
    
    # The meeting must lie within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add busy constraints for Willie for the current day.
    for (busy_start, busy_end) in willie_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Add busy constraints for Dorothy for the current day.
    for (busy_start, busy_end) in dorothy_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Try to find a valid start time by iterating minute-by-minute.
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
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
    print(f"A valid meeting time is on {day_names.get(meeting_day)} from "
          f"{start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")