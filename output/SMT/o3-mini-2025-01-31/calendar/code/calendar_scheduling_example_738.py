from z3 import Solver, Int, Or, sat

# Meeting duration: 30 minutes
duration = 30
# Meeting start time in minutes (from midnight)
start = Int("start")

# Work hours (in minutes from midnight)
WORK_START = 540   # 9:00
WORK_END = 1020    # 17:00

# Days encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday.
# Pamela would like to avoid meetings on Monday and Tuesday, so try Wednesday first.
candidate_days = [2, 0, 1]

# Define busy schedules (times in minutes from midnight)
# Sara's busy schedule:
sara_busy = {
    0: [  # Monday
        (540, 600),   # 9:00 - 10:00
        (660, 690),   # 11:00 - 11:30
        (780, 870),   # 13:00 - 14:30
        (930, 960)    # 15:30 - 16:00
    ],
    1: [  # Tuesday
        (570, 600),   # 9:30 - 10:00
        (630, 660),   # 10:30 - 11:00
        (690, 720),   # 11:30 - 12:00
        (840, 870),   # 14:00 - 14:30
        (960, 990)    # 16:00 - 16:30
    ],
    2: [  # Wednesday
        (570, 600),   # 9:30 - 10:00
        (720, 750),   # 12:00 - 12:30
        (840, 870),   # 14:00 - 14:30
        (930, 1020)   # 15:30 - 17:00
    ]
}

# Pamela's busy schedule:
pamela_busy = {
    0: [  # Monday
        (540, 780),   # 9:00 - 13:00
        (870, 930),   # 14:30 - 15:30
        (990, 1020)   # 16:30 - 17:00
    ],
    1: [  # Tuesday
        (540, 570),   # 9:00 - 9:30
        (600, 630),   # 10:00 - 10:30
        (690, 780),   # 11:30 - 13:00
        (810, 840),   # 13:30 - 14:00
        (960, 990)    # 16:00 - 16:30
    ],
    2: [  # Wednesday
        (540, 660),   # 9:00 - 11:00
        (720, 840),   # 12:00 - 14:00
        (960, 1020)   # 16:00 - 17:00
    ]
}

# Helper function: meeting [start, start+duration) must not overlap a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None       # day number (0=Mon, 1=Tue, 2=Wed)
meeting_start_val = None  # meeting start time (in minutes)

# Iterate over candidate days using the preferred order.
for day in candidate_days:
    solver = Solver()
    
    # Meeting must be within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Preference constraint: Sara wants to avoid meetings on Wednesday before 14:00.
    # If day is Wednesday (day == 2), enforce start >= 14:00 (840 minutes).
    if day == 2:
        solver.add(start >= 840)
    
    # Add Sara's busy constraints for the given day.
    for interval in sara_busy.get(day, []):
        busy_start, busy_end = interval
        solver.add(non_overlap(busy_start, busy_end))
    
    # Add Pamela's busy constraints for the given day.
    for interval in pamela_busy.get(day, []):
        busy_start, busy_end = interval
        solver.add(non_overlap(busy_start, busy_end))
    
    # Try to find a valid start time (earliest possible) by iterating minute by minute.
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
    print(f"A valid meeting time is on {day_names.get(meeting_day, 'Unknown')} from "
          f"{start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")