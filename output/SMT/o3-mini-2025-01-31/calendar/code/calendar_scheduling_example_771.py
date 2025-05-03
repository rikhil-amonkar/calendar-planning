from z3 import Solver, Int, Or, sat

# Meeting duration: 30 minutes
duration = 30

# Define the meeting start time (in minutes after midnight)
start = Int("start")

# Working hours: 9:00 = 540 minutes, 17:00 = 1020 minutes.
WORK_START = 540
WORK_END = 1020

# Day encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday.
candidate_days = [0, 1, 2]

# Ann's busy schedule (in minutes):
# Monday: 12:00-13:00 -> (720,780), 15:30-16:30 -> (930,990)
# Tuesday: 9:00-9:30   -> (540,570), 10:30-11:30 -> (630,690), 13:00-15:00 -> (780,900)
# Wednesday: 10:30-11:30 -> (630,690), 13:00-13:30 -> (780,810), 14:00-14:30 -> (840,870),
#            16:00-16:30 -> (960,990)
ann_busy = {
    0: [(720, 780), (930, 990)],
    1: [(540, 570), (630, 690), (780, 900)],
    2: [(630, 690), (780, 810), (840, 870), (960, 990)]
}

# Susan's busy schedule (in minutes):
# Monday: 10:00-10:30 -> (600,630), 11:00-12:00 -> (660,720), 12:30-13:00 -> (750,780),
#         13:30-14:00 -> (810,840), 15:00-16:00 -> (900,960), 16:30-17:00 -> (990,1020)
# Tuesday: 9:00-10:30 -> (540,630), 11:00-11:30 -> (660,690), 12:00-12:30 -> (720,750),
#          13:00-13:30 -> (780,810), 14:00-14:30 -> (840,870), 15:00-16:00 -> (900,960)
# Wednesday: 9:00-10:00 -> (540,600), 10:30-13:30 -> (630,810), 14:00-15:00 -> (840,900),
#            16:00-16:30 -> (960,990)
susan_busy = {
    0: [(600,630), (660,720), (750,780), (810,840), (900,960), (990,1020)],
    1: [(540,630), (660,690), (720,750), (780,810), (840,870), (900,960)],
    2: [(540,600), (630,810), (840,900), (960,990)]
}

# Preference: Ann cannot meet on Tuesday after 12:30.
def apply_ann_preference(day, solver):
    if day == 1:
        # Meeting must finish no later than 12:30 (750 minutes)
        solver.add(start + duration <= 750)

# Preference: Susan does not want to meet on Monday.
def apply_susan_preference(day, solver):
    if day == 0:
        solver.add(False)  # Disallow Monday by adding a contradiction

# Helper: Ensure the meeting interval [start, start + duration) does not overlap with a busy interval [busy_start, busy_end).
def non_overlap(busy_start, busy_end):
    # Either the meeting finishes before the busy interval starts or starts after it ends.
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None
meeting_start_val = None

# Process candidate days: Monday, Tuesday, Wednesday.
for day in candidate_days:
    solver = Solver()
    
    # Meeting must lie within working hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Apply preferences:
    apply_susan_preference(day, solver)
    apply_ann_preference(day, solver)
    
    # Add Ann's busy schedule constraints for the day.
    for b_start, b_end in ann_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Add Susan's busy schedule constraints for the day.
    for b_start, b_end in susan_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Try to find a valid start time by iterating minute-by-minute.
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t)
        if solver.check() == sat:
            meeting_start_val = t
            meeting_day = day
            found = True
            solver.pop()  # remove the push
            break
        solver.pop()
    
    if found:
        break

if found:
    meeting_end_val = meeting_start_val + duration
    start_hr, start_min = divmod(meeting_start_val, 60)
    end_hr, end_min = divmod(meeting_end_val, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
    print(f"A valid meeting time is on {day_names[meeting_day]} from {start_hr:02d}:{start_min:02d} to {end_hr:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")