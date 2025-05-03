from z3 import Solver, Int, Or, sat

# Meeting duration in minutes (30 minutes)
duration = 30

# Meeting start time variable (in minutes after midnight)
start = Int("start")

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Days encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday.
candidate_days = [0, 1, 2]

# Jennifer's busy schedule (in minutes)
# Monday: 12:30-13:00 -> (750,780), 14:30-15:00 -> (870,900), 16:00-16:30 -> (960,990)
# Tuesday: 12:30-13:00 -> (750,780)
# Wednesday: 12:30-13:00 -> (750,780), 15:30-16:00 -> (930,960)
jennifer_busy = {
    0: [(750,780), (870,900), (960,990)],
    1: [(750,780)],
    2: [(750,780), (930,960)]
}

# Christine's busy schedule (in minutes)
# Monday: 10:00-11:00 -> (600,660), 12:00-14:30 -> (720,870), 16:00-16:30 -> (960,990)
# Tuesday: 10:00-10:30 -> (600,630), 11:00-11:30 -> (660,690),
#          12:00-13:00 -> (720,780), 13:30-15:30 -> (810,930), 16:00-16:30 -> (960,990)
# Wednesday: 9:00-9:30 -> (540,570), 10:00-10:30 -> (600,630),
#            11:30-13:30 -> (690,810), 14:00-15:30 -> (840,930), 16:00-17:00 -> (960,1020)
christine_busy = {
    0: [(600,660), (720,870), (960,990)],
    1: [(600,630), (660,690), (720,780), (810,930), (960,990)],
    2: [(540,570), (600,630), (690,810), (840,930), (960,1020)]
}

# Helper function:
# Ensure that the meeting [start, start+duration) does not overlap with a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None       # day index (0,1, or 2)
meeting_start_val = None # meeting start time in minutes after midnight

# Iterate through candidate days in order (earliest day first)
for day in candidate_days:
    solver = Solver()
    # The meeting must be scheduled within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Jennifer's busy constraints for the day.
    for b_start, b_end in jennifer_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Add Christine's busy constraints for the day.
    for b_start, b_end in christine_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Search for the earliest valid start time on this day.
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t)
        if solver.check() == sat:
            meeting_start_val = t
            meeting_day = day
            found = True
            solver.pop()  # Remove the temporary assignment
            break
        solver.pop()
    
    if found:
        break

if found:
    meeting_end_val = meeting_start_val + duration
    # Convert minutes into HH:MM format.
    start_hour, start_min = divmod(meeting_start_val, 60)
    end_hour, end_min = divmod(meeting_end_val, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
    print(f"A valid meeting time is on {day_names[meeting_day]} from {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")