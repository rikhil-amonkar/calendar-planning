from z3 import Solver, Int, Or, sat

# Meeting duration in minutes (60 minutes)
duration = 60

# Meeting start time variable (in minutes after midnight)
start = Int("start")

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Days encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday.
candidate_days = [0, 1, 2]

# Debra's busy schedule (in minutes)
# Monday: 9:00-9:30 -> (540,570), 10:00-11:00 -> (600,660), 12:00-12:30 -> (720,750),
#         13:30-14:00 -> (810,840), 15:00-15:30 -> (900,930)
# Tuesday: 13:00-14:30 -> (780,870), 15:30-16:00 -> (930,960)
# Wednesday: 11:00-11:30 -> (660,690), 12:00-12:30 -> (720,750), 13:30-14:00 -> (810,840), 15:00-15:30 -> (900,930)
debra_busy = {
    0: [(540,570), (600,660), (720,750), (810,840), (900,930)],
    1: [(780,870), (930,960)],
    2: [(660,690), (720,750), (810,840), (900,930)]
}

# Maria's busy schedule (in minutes)
# Monday: 9:30-12:00 -> (570,720), 12:30-14:00 -> (750,840), 14:30-17:00 -> (870,1020)
# Tuesday: 9:00-10:00 -> (540,600), 10:30-11:30 -> (630,690), 12:30-13:00 -> (750,780), 13:30-17:00 -> (810,1020)
# Wednesday: 9:30-11:30 -> (570,690), 12:00-13:00 -> (720,780), 13:30-17:00 -> (810,1020)
maria_busy = {
    0: [(570,720), (750,840), (870,1020)],
    1: [(540,600), (630,690), (750,780), (810,1020)],
    2: [(570,690), (720,780), (810,1020)]
}

# Helper function:
# Ensures that the meeting [start, start+duration) does not overlap 
# with a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None       # day index (0, 1, or 2)
meeting_start_val = None # meeting start time in minutes after midnight

for day in candidate_days:
    solver = Solver()
    
    # Meeting must be within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Debra's busy constraints for the day.
    for b_start, b_end in debra_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Add Maria's busy constraints for the day.
    for b_start, b_end in maria_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Look for the earliest valid start time on this day.
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t)
        if solver.check() == sat:
            meeting_start_val = t
            meeting_day = day
            found = True
            solver.pop()  # remove temporary assignment
            break
        solver.pop()
    
    if found:
        break

if found:
    meeting_end_val = meeting_start_val + duration
    start_hour, start_min = divmod(meeting_start_val, 60)
    end_hour, end_min = divmod(meeting_end_val, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
    print(f"A valid meeting time is on {day_names[meeting_day]} from {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")