from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 60  # meeting duration in minutes (one hour)
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Days encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday
days = [0, 1, 2]

# Gerald's busy schedule (times in minutes from midnight)
gerald_busy = {
    0: [
        (10*60, 10*60 + 30),   # Monday: 10:00 to 10:30 -> (600,630)
        (12*60, 12*60 + 30),   # Monday: 12:00 to 12:30 -> (720,750)
        (14*60 + 30, 15*60),   # Monday: 14:30 to 15:00 -> (870,900)
        (16*60 + 30, 17*60)    # Monday: 16:30 to 17:00 -> (990,1020)
    ],
    1: [
        (12*60, 12*60 + 30),   # Tuesday: 12:00 to 12:30 -> (720,750)
        (14*60 + 30, 15*60),   # Tuesday: 14:30 to 15:00 -> (870,900)
        (15*60 + 30, 16*60 + 30)  # Tuesday: 15:30 to 16:30 -> (930,990)
    ],
    2: [
        (9*60, 9*60 + 30),     # Wednesday: 9:00 to 9:30 -> (540,570)
        (11*60 + 30, 12*60)    # Wednesday: 11:30 to 12:00 -> (690,720)
    ]
}

# Adam's busy schedule (times in minutes from midnight)
adam_busy = {
    0: [
        (WORK_START, WORK_END)  # Monday: busy entire day, 9:00 to 17:00
    ],
    1: [
        (9*60, 10*60 + 30),   # Tuesday: 9:00 to 10:30 -> (540,630)
        (11*60, 15*60),       # Tuesday: 11:00 to 15:00 -> (660,900)
        (16*60, WORK_END)     # Tuesday: 16:00 to 17:00 -> (960,1020)
    ],
    2: [
        (9*60, 13*60),        # Wednesday: 9:00 to 13:00 -> (540,780)
        (14*60 + 30, 15*60 + 30),  # Wednesday: 14:30 to 15:30 -> (870,930)
        (16*60 + 30, WORK_END)     # Wednesday: 16:30 to 17:00 -> (990,1020)
    ]
}

# Additional constraint: Adam cannot meet on Wednesday after 14:30.
# This implies that if the meeting is on Wednesday (day 2), then the meeting must finish by 14:30,
# i.e., start + duration <= 14:30, which in minutes is 14*60+30 = 870.
def meeting_end_limit(day):
    if day == 2:
        return start + duration <= 870  # meeting must end by 14:30
    return True  # no additional limit for other days

# Helper function: Meeting [start, start+duration) must not overlap with a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None  # Will be 0 (Monday), 1 (Tuesday), or 2 (Wednesday)
meeting_start = None

# Iterate days in order: Monday, Tuesday, Wednesday.
for day in days:
    solver = Solver()
    # The meeting must be within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    # Add Adam's additional constraint if the day is Wednesday.
    solver.add(meeting_end_limit(day))
    
    # Add Gerald's busy constraints for the day.
    for b_start, b_end in gerald_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Add Adam's busy constraints for the day.
    for b_start, b_end in adam_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
        
    # Search for the earliest meeting start time within the work day.
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