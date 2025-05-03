from z3 import Solver, Int, Or, sat

# Meeting duration: 60 minutes.
duration = 60

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 9 * 60     # 540 minutes
WORK_END   = 17 * 60    # 1020 minutes

# Candidate days represented as integers:
# Monday = 0, Tuesday = 1, Wednesday = 2, Thursday = 3.
candidate_days = [0, 1, 2, 3]

# Busy schedules for Amy (times in minutes since midnight):
# Monday: 10:30-11:00 -> (630,660); 12:00-12:30 -> (720,750); 13:30-14:00 -> (810,840); 15:30-16:00 -> (930,960)
# Tuesday: 11:00-12:00 -> (660,720)
# Wednesday: 10:00-10:30 -> (600,630)
# Thursday: 10:00-10:30 -> (600,630); 13:00-13:30 -> (780,810); 15:00-15:30 -> (900,930)
amy_busy = {
    0: [(630, 660), (720, 750), (810, 840), (930, 960)],
    1: [(660, 720)],
    2: [(600, 630)],
    3: [(600, 630), (780, 810), (900, 930)]
}

# Busy schedules for Michelle:
# Monday: 9:00-9:30 -> (540,570); 10:30-12:30 -> (630,750); 13:00-14:00 -> (780,840); 14:30-17:00 -> (870,1020)
# Tuesday: 9:00-10:00 -> (540,600); 10:30-11:30 -> (630,690); 12:30-13:00 -> (750,780);
#          13:30-14:00 -> (810,840); 14:30-15:30 -> (870,930); 16:00-16:30 -> (960,990)
# Wednesday: 9:00-9:30 -> (540,570); 10:00-10:30 -> (600,630); 11:00-11:30 -> (660,690);
#            12:00-12:30 -> (720,750); 13:00-13:30 -> (780,810); 14:30-15:00 -> (870,900); 16:00-16:30 -> (960,990)
# Thursday: 9:00-9:30 -> (540,570); 10:00-10:30 -> (600,630); 11:00-12:00 -> (660,720);
#           13:00-13:30 -> (780,810); 15:00-15:30 -> (900,930); 16:00-17:00 -> (960,1020)
michelle_busy = {
    0: [(540,570), (630,750), (780,840), (870,1020)],
    1: [(540,600), (630,690), (750,780), (810,840), (870,930), (960,990)],
    2: [(540,570), (600,630), (660,690), (720,750), (780,810), (870,900), (960,990)],
    3: [(540,570), (600,630), (660,720), (780,810), (900,930), (960,1020)]
}

solution_found = False
selected_day = None
selected_start = None

# Helper function: 
# Returns a constraint ensuring that a meeting starting at 'start_var' with given duration
# does not overlap with a busy interval [busy_start, busy_end).
def no_overlap(busy_start, busy_end, start_var):
    return Or(start_var + duration <= busy_start, start_var >= busy_end)

# The preferences are:
#   - Amy would rather not meet on Wednesday. So we disallow day 2.
#   - Michelle would like to avoid more meetings on Monday. So we disallow day 0.
# Also, the group would like to meet at their earliest availability (first in order of day and time).
for day in candidate_days:
    solver = Solver()
    start = Int("start")
    
    # The meeting must be fully within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Apply preferences as hard constraints:
    if day == 2:  # Wednesday for Amy - avoid meeting.
        solver.add(False)
    if day == 0:  # Monday for Michelle - avoid meeting.
        solver.add(False)
    
    # Add constraints for Amy's busy intervals for this day.
    for (busy_start, busy_end) in amy_busy.get(day, []):
        solver.add(no_overlap(busy_start, busy_end, start))
    
    # Add constraints for Michelle's busy intervals for this day.
    for (busy_start, busy_end) in michelle_busy.get(day, []):
        solver.add(no_overlap(busy_start, busy_end, start))
    
    # Search for an available time, iterating minute-by-minute.
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t)
        if solver.check() == sat:
            selected_start = t
            selected_day = day
            solution_found = True
            solver.pop()
            break
        solver.pop()
    
    if solution_found:
        break

if solution_found:
    selected_end = selected_start + duration
    # Convert minutes into hours and minutes.
    start_hour, start_min = divmod(selected_start, 60)
    end_hour, end_min = divmod(selected_end, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(day_names[selected_day], start_hour, start_min, end_hour, end_min))
else:
    print("No valid meeting time could be found that satisfies all constraints.")