from z3 import Solver, Int, Or, sat

# Meeting duration: 60 minutes
duration = 60
# Meeting start time variable (in minutes from midnight)
start = Int("start")

# Define work hours in minutes (9:00 to 17:00)
WORK_START = 540   # 9 * 60
WORK_END = 1020    # 17 * 60

# Days encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday.
# Constraints:
# • Jordan cannot meet on Tuesday  ==> day != 1
# • Bobby does not want to meet on Monday ==> prefer non-Monday if possible
# • If meeting is on Wednesday, it must be before 12:00 (i.e. the meeting must finish by 12:00)
#
# Given these, we first try Wednesday (day 2) and then Monday (day 0) if needed.
candidate_days = [2, 0]

# Busy schedules (times in minutes from midnight)

# Jordan's busy schedule:
jordan_busy = {
    2: [  # Wednesday
        (630, 660),   # 10:30 - 11:00
        (720, 750)    # 12:00 - 12:30
    ],
    0: [],  # Monday: no busy intervals given for Jordan
    1: []   # Tuesday: Jordan cannot meet anyway (we won’t select Tuesday)
}

# Bobby's busy schedule:
bobby_busy = {
    0: [  # Monday
        (570, 600),   # 9:30 - 10:00
        (690, 720),   # 11:30 - 12:00
        (810, 840),   # 13:30 - 14:00
        (870, 900),   # 14:30 - 15:00
        (930, 960),   # 15:30 - 16:00
        (990, 1020)   # 16:30 - 17:00
    ],
    1: [  # Tuesday
        (570, 750),   # 9:30 - 12:30
        (780, 840),   # 13:00 - 14:00
        (900, 930),   # 15:00 - 15:30
        (960, 990)    # 16:00 - 16:30
    ],
    2: [  # Wednesday
        (540, 570),   # 9:00 - 9:30
        (600, 630),   # 10:00 - 10:30
        (720, 750),   # 12:00 - 12:30
        (780, 810),   # 13:00 - 13:30
        (840, 960)    # 14:00 - 16:00
    ]
}

# Helper: meeting interval [start, start + duration) must not overlap
# with a busy interval [busy_start, busy_end).
def non_overlap(busy_start, busy_end):
    # Either the meeting ends at or before the busy period starts
    # or starts at or after the busy period ends.
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None       # day chosen: 0 (Monday), 1 (Tuesday), or 2 (Wednesday)
meeting_start_val = None # meeting start time in minutes from midnight

# Iterate over candidate days in the preferred order.
for day in candidate_days:
    # Skip Tuesday explicitly if it appears
    if day == 1:
        continue

    solver = Solver()
    # Meeting must be within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Additional constraint if meeting is on Wednesday: it must be before 12:00.
    # Since duration is 60 minutes, meeting_end must be <= 720 minutes.
    if day == 2:
        solver.add(start + duration <= 720)
    
    # Add busy constraints for Jordan.
    for (busy_start, busy_end) in jordan_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Add busy constraints for Bobby.
    for (busy_start, busy_end) in bobby_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Search for a valid start time (earliest possible) minute-by-minute.
    # Note: For Wednesday, we already limited start + duration <= 720.
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