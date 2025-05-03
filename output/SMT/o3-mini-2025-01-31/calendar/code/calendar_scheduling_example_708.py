from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30  # meeting duration in minutes (half an hour)
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Days: 0 = Monday, 1 = Tuesday, 2 = Wednesday

# Billy's busy schedule (times in minutes):
billy_busy = {
    0: [(16 * 60, 16 * 60 + 30)],  # Monday: 16:00 to 16:30  -> [960, 990)
    1: [(15 * 60, 15 * 60 + 30)]   # Tuesday: 15:00 to 15:30 -> [900, 930)
    # No busy times indicated for Wednesday.
}

# Jean's busy schedule (times in minutes):
jean_busy = {
    0: [
        (540, 750),    # Monday: 9:00 to 12:30 -> [540,750)
        (810, 900),    # Monday: 13:30 to 15:00 -> [810,900)
        (930, 1020)    # Monday: 15:30 to 17:00 -> [930,1020)
    ],
    1: [
        (540, 1020)    # Tuesday: 9:00 to 17:00 -> [540,1020)
    ],
    2: [
        (570, 1020)    # Wednesday: 9:30 to 17:00 -> [570,1020)
    ]
}

# Jean’s meeting preferences:
# - If meeting is on Monday, Jean would rather not meet after 13:30.
#   We interpret this to mean that on Monday the meeting must end by 13:30 (13*60+30 = 810 minutes).

def non_overlap(busy_start, busy_end):
    # The meeting interval [start, start+duration) must not overlap with [busy_start, busy_end)
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None  # 0 = Monday, 1 = Tuesday, 2 = Wednesday
meeting_start = None

# Given Jean's busy schedule on Tuesday (busy all day) and her preference against Wednesday,
# we prefer to schedule on Monday if possible (meeting must finish by 13:30), then try Wednesday.
prioritized_days = [0, 2]

for day in prioritized_days:
    solver = Solver()
    
    # Meeting must be within work hours:
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # If the meeting is on Monday, enforce Jean’s preference:
    # Meeting must end by 13:30 (i.e. start + duration <= 810).
    if day == 0:
        solver.add(start + duration <= 810)
        
    # Add Billy's busy constraints for the chosen day.
    for b_start, b_end in billy_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Add Jean's busy constraints for the chosen day.
    for j_start, j_end in jean_busy.get(day, []):
        solver.add(non_overlap(j_start, j_end))
    
    # We search for the earliest available time slot by iterating the possible start times.
    # Compute the latest possible start time within work hours for a meeting.
    latest_start = WORK_END - duration
    for t in range(WORK_START, latest_start + 1):
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