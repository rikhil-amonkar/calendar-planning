from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30  # half an hour
start = Int("start")  # meeting start time (in minutes from midnight)

# Work hours in minutes: 9:00 = 540, 17:00 = 1020
WORK_START = 540
WORK_END = 1020

# Days encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday.
# Lisa does not want to meet on Monday,
# so we prefer Tuesday first, then Wednesday, then Monday.
candidate_days = [1, 2, 0]

# Busy schedules (times in minutes from midnight)

# Lisa's busy schedule:
lisa_busy = {
    0: [  # Monday
        (570, 600),   # 9:30 - 10:00
        (630, 660),   # 10:30 - 11:00
        (720, 750),   # 12:00 - 12:30
        (780, 810),   # 13:00 - 13:30
        (840, 870),   # 14:00 - 14:30
        (900, 990)    # 15:00 - 16:30
    ],
    1: [  # Tuesday
        (570, 600),   # 9:30 - 10:00
        (750, 810),   # 12:30 - 13:30
        (870, 960),   # 14:30 - 16:00
        (990, 1020)   # 16:30 - 17:00
    ],
    2: [  # Wednesday
        (630, 660),   # 10:30 - 11:00
        (690, 750),   # 11:30 - 12:30
        (870, 930),   # 14:30 - 15:30
        (960, 1020)   # 16:00 - 17:00
    ]
}

# Jerry's busy schedule:
jerry_busy = {
    0: [  # Monday
        (570, 600),   # 9:30 - 10:00
        (630, 660),   # 10:30 - 11:00
        (720, 750),   # 12:00 - 12:30
        (780, 870),   # 13:00 - 14:30
        (990, 1020)   # 16:30 - 17:00
    ],
    1: [  # Tuesday
        (540, 1020)   # busy all day (9:00 - 17:00)
    ],
    2: [  # Wednesday
        (540, 780),   # 9:00 - 13:00
        (810, 840),   # 13:30 - 14:00
        (870, 960),   # 14:30 - 16:00
        (990, 1020)   # 16:30 - 17:00
    ]
}

# Helper function: ensure meeting interval [start, start+duration)
# does not overlap with a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None       # day chosen: 0,1,2
meeting_start_val = None # meeting start time in minutes

# Iterate over candidate days in the preferred order.
for day in candidate_days:
    solver = Solver()
    
    # Meeting should be within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # If the meeting is on Wednesday, Lisa does not want it before 13:30.
    if day == 2:
        solver.add(start >= 810)  # 13:30 in minutes
    
    # Add Lisa's busy constraints for the day.
    for interval in lisa_busy.get(day, []):
        b_start, b_end = interval
        solver.add(non_overlap(b_start, b_end))
    
    # Add Jerry's busy constraints for the day.
    for interval in jerry_busy.get(day, []):
        b_start, b_end = interval
        solver.add(non_overlap(b_start, b_end))
    
    # Try to get the earliest possible start time by iterating over minutes.
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