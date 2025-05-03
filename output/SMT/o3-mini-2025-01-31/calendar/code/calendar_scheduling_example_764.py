from z3 import Solver, Int, Or, sat

# Meeting duration: 30 minutes
duration = 30

# Meeting start variable (in minutes from midnight)
start = Int("start")

# Define work hours in minutes (9:00 - 17:00)
WORK_START = 540
WORK_END = 1020

# Day encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday
candidate_days = [0, 1, 2]

# Busy schedules in minutes (start, end)
# Diana's busy schedule:
# Monday: 11:00-11:30 -> (660,690), 12:00-12:30 -> (720,750)
# Tuesday: 9:00-10:30 -> (540,630), 12:00-13:00 -> (720,780), 
#          13:30-14:00 -> (810,840), 14:30-15:00 -> (870,900), 15:30-16:30 -> (930,990)
# Wednesday: 9:00-10:30 -> (540,630), 13:30-16:30 -> (810,990)
diana_busy = {
    0: [(660, 690), (720, 750)],
    1: [(540, 630), (720, 780), (810, 840), (870, 900), (930, 990)],
    2: [(540, 630), (810, 990)]
}

# Denise's busy schedule:
# Monday: 9:00-10:00 -> (540,600), 10:30-11:00 -> (630,660), 12:30-14:00 -> (750,840), 14:30-16:00 -> (870,960)
# Tuesday: 9:00-17:00 -> (540,1020)
# Wednesday: 9:00-9:30 -> (540,570), 10:00-10:30 -> (600,630), 11:30-14:30 -> (690,870), 15:00-16:30 -> (900,990)
denise_busy = {
    0: [(540, 600), (630, 660), (750, 840), (870, 960)],
    1: [(540, 1020)],
    2: [(540, 570), (600, 630), (690, 870), (900, 990)]
}

# Diana cannot meet on Wednesday.
cannot_meet_on = {2}  # Wednesday

# Helper function: meeting time [start, start+duration) does NOT overlap with busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None          # Day index for meeting
meeting_start_val = None    # Meeting start time in minutes after midnight

# Iterate over candidate days in order (which gives the earliest available day)
for day in candidate_days:
    # If Diana cannot meet on this day, skip it.
    if day in cannot_meet_on:
        continue

    solver = Solver()
    # The meeting must lie within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)

    # Add Diana's busy constraints for that day.
    for b_start, b_end in diana_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
        
    # Add Denise's busy constraints for that day.
    for b_start, b_end in denise_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Try every minute from WORK_START to (WORK_END - duration) to get the earliest possible slot.
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
    start_hr, start_min = divmod(meeting_start_val, 60)
    end_hr, end_min = divmod(meeting_end_val, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
    print(f"A valid meeting time is on {day_names[meeting_day]} from {start_hr:02d}:{start_min:02d} to {end_hr:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")