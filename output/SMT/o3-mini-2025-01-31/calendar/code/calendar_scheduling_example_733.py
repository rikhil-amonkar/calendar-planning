from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30  # meeting duration in minutes (half an hour)
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Days encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday.
# Note: George prefers not to meet on Monday after 12:30, and Carl prefers to avoid Tuesday and Wednesday.
# We'll try days in the order [Monday, Tuesday, Wednesday] so that if Monday has an available slot it is chosen.
candidate_days = [0, 1, 2]

# Busy schedules are represented as intervals [busy_start, busy_end)
# All times are in minutes from midnight.

# George's busy schedule:
george_busy = {
    0: [  # Monday
        (600, 630),    # 10:00 to 10:30
        (720, 780),    # 12:00 to 13:00
        (810, 870),    # 13:30 to 14:30
        (900, 990)     # 15:00 to 16:30
    ],
    1: [  # Tuesday
        (600, 630),    # 10:00 to 10:30
        (810, 870)     # 13:30 to 14:30
    ],
    2: [  # Wednesday
        (540, 570),    # 9:00 to 9:30
        (600, 660),    # 10:00 to 11:00
        (810, 900),    # 13:30 to 15:00
        (930, 960)     # 15:30 to 16:00
    ]
}

# Carl's busy schedule:
carl_busy = {
    0: [  # Monday
        (630, 660),    # 10:30 to 11:00
        (690, 720),    # 11:30 to 12:00
        (780, 840),    # 13:00 to 14:00
        (990, 1020)    # 16:30 to 17:00
    ],
    1: [  # Tuesday
        (540, 570),    # 9:00 to 9:30
        (600, 630),    # 10:00 to 10:30
        (660, 750),    # 11:00 to 12:30
        (810, 870),    # 13:30 to 14:30
        (930, 1020)    # 15:30 to 17:00
    ],
    2: [  # Wednesday
        (570, 630),    # 9:30 to 10:30
        (660, 810),    # 11:00 to 13:30
        (840, 870),    # 14:00 to 14:30
        (990, 1020)    # 16:30 to 17:00
    ]
}

# Helper function: Meeting interval [start, start+duration) must not overlap a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None       # day (0,1,2) when meeting is scheduled
meeting_start_val = None # meeting start time in minutes from midnight

# Iterate over candidate days in order.
for day in candidate_days:
    solver = Solver()
    
    # The meeting must fit within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add additional constraint: George does not want meetings on Monday after 12:30.
    if day == 0:
        # 12:30 is 750 minutes. We require that the meeting finishes by 12:30.
        solver.add(start + duration <= 750)
    
    # Add Carl's preference: He would like to avoid meetings on Tuesday and Wednesday.
    # We are iterating in order; so if Monday works that's our best outcome.
    # For Tuesday and Wednesday, no additional hard constraint is needed,
    # but note that they are lower in our candidate ordering.
    
    # Add George's busy time constraints for this day.
    for busy_interval in george_busy.get(day, []):
        busy_start, busy_end = busy_interval
        solver.add(non_overlap(busy_start, busy_end))
    
    # Add Carl's busy time constraints for this day.
    for busy_interval in carl_busy.get(day, []):
        busy_start, busy_end = busy_interval
        solver.add(non_overlap(busy_start, busy_end))
    
    # Search for the earliest available time slot minute-by-minute.
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