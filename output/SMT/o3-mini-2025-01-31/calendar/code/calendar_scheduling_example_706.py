from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 60  # meeting duration in minutes (1 hour)
start = Int("start")  # meeting start time (in minutes from midnight)

# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Days: 0 = Monday, 1 = Tuesday, 2 = Wednesday

# Gregory's busy schedule (times in minutes):
gregory_busy = {
    0: [(15*60+30, 16*60+30)],  # Monday: 15:30 to 16:30 -> (930, 990)
    1: [(540, 570),            # Tuesday: 9:00 to 9:30 -> (540, 570)
        (11*60+30, 12*60),     # Tuesday: 11:30 to 12:00 -> (690, 720)
        (14*60, 14*60+30),     # Tuesday: 14:00 to 14:30 -> (840, 870)
        (15*60, 16*60),        # Tuesday: 15:00 to 16:00 -> (900, 960)
        (16*60+30, 17*60)],    # Tuesday: 16:30 to 17:00 -> (990, 1020)
    2: [(540, 570),            # Wednesday: 9:00 to 9:30 -> (540, 570)
        (10*60, 11*60),        # Wednesday: 10:00 to 11:00 -> (600, 660)
        (11*60+30, 13*60),      # Wednesday: 11:30 to 13:00 -> (690, 780)
        (13*60+30, 14*60+30)]   # Wednesday: 13:30 to 14:30 -> (810, 870)
}

# Patricia's busy schedule (times in minutes):
patricia_busy = {
    0: [(540, 570),            # Monday: 9:00 to 9:30 -> (540, 570)
        (600, 630),            # Monday: 10:00 to 10:30 -> (600, 630)
        (11*60+30, 15*60)],     # Monday: 11:30 to 15:00 -> (690, 900)
    1: [(540, 630),            # Tuesday: 9:00 to 10:30 -> (540, 630)
        (11*60, 11*60+30),     # Tuesday: 11:00 to 11:30 -> (660, 690)
        (12*60, 14*60+30),     # Tuesday: 12:00 to 14:30 -> (720, 870)
        (15*60, 15*60+30),     # Tuesday: 15:00 to 15:30 -> (900, 930)
        (16*60+30, 17*60)],    # Tuesday: 16:30 to 17:00 -> (990, 1020)
    2: [(540, 570),            # Wednesday: 9:00 to 9:30 -> (540, 570)
        (10*60, 12*60+30),     # Wednesday: 10:00 to 12:30 -> (600, 750)
        (13*60+30, 16*60),     # Wednesday: 13:30 to 16:00 -> (810, 960)
        (16*60+30, 17*60)]     # Wednesday: 16:30 to 17:00 -> (990, 1020)
}

def non_overlap(busy_start, busy_end):
    # Meeting interval [start, start+duration) must not overlap with [busy_start, busy_end)
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None     # 0 = Monday, 1 = Tuesday, 2 = Wednesday
meeting_start = None

# We'll check days in order: Monday, then Tuesday, then Wednesday.
for day in [0, 1, 2]:
    solver = Solver()
    # Meeting must be within work hours
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Gregory's busy constraints for the given day.
    for b_start, b_end in gregory_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
        
    # Add Patricia's busy constraints for the given day.
    for b_start, b_end in patricia_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Check possible meeting start times in ascending order to get the earliest available slot.
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
    day_name = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}[meeting_day]
    print(f"A valid meeting time is on {day_name} from {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")