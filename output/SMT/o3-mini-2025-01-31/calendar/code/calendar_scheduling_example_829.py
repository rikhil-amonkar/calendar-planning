from z3 import Solver, Int, Or, sat

# Meeting duration in minutes (30 minutes)
duration = 30

# Work hours in minutes: 9:00 (540) to 17:00 (1020)
WORK_START = 9 * 60    # 540
WORK_END   = 17 * 60   # 1020

# Days: Monday = 0, Tuesday = 1, Wednesday = 2, Thursday = 3.
# Based on extra constraints:
# - Rachel cannot meet on Monday or Tuesday.
# - If meeting on Wednesday, it must be scheduled so that it finishes by 10:00.
# - Carolyn would like to avoid more meetings on Thursday.
# To respect preferences, we try Wednesday first then Thursday.
candidate_days = [2, 3, 0, 1]

# Rachel's busy intervals (in minutes) by day:
# Monday: 9:00-9:30, 11:30-12:30, 13:30-14:00, 14:30-15:00, 16:00-16:30
# Tuesday: 11:00-12:00, 12:30-13:00, 16:00-17:00
# Wednesday: 9:30-10:00, 12:00-12:30, 15:00-15:30, 16:00-17:00
# Thursday: 10:00-10:30, 11:00-11:30, 14:30-15:00, 16:00-16:30
rachel_busy = {
    0: [(540,570), (690,750), (810,840), (870,900), (960,990)],
    1: [(660,720), (750,780), (960,1020)],
    2: [(570,600), (720,750), (900,930), (960,1020)],
    3: [(600,630), (660,690), (870,900), (960,990)]
}

# Carolyn's busy intervals (in minutes) by day:
# Monday: 11:00-14:00, 14:30-15:00
# Tuesday: 9:00-9:30, 10:30-17:00
# Wednesday: 9:30-14:00, 14:30-15:00, 15:30-17:00
# Thursday: 9:00-9:30, 10:00-13:00, 13:30-15:00
carolyn_busy = {
    0: [(660,840), (870,900)],
    1: [(540,570), (630,1020)],
    2: [(570,840), (870,900), (930,1020)],
    3: [(540,570), (600,780), (810,900)]
}

solution_found = False
selected_day = None
selected_start = None

# Helper function: The meeting with start time 'start_var' of length "duration"
# does not overlap a busy interval [busy_start, busy_end)
def no_overlap(busy_start, busy_end, start_var):
    return Or(start_var + duration <= busy_start, start_var >= busy_end)

# We'll search through days in the candidate order.
# Additional constraints:
# - Rachel cannot meet on Monday (day==0) or Tuesday (day==1).
# - On Wednesday (day==2), the meeting must finish by 10:00 (600 minutes).
# - Carolyn would prefer to avoid Thursday (day==3) if possible, so we try it later.
for day in candidate_days:
    solver = Solver()
    start = Int("start")
    
    # Meeting must be within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Rachel's day availability constraint
    if day in [0, 1]:
        # Rachel cannot meet on Monday or Tuesday.
        solver.add(False)
    elif day == 2:
        # On Wednesday, Rachel insists that the meeting not be after 10:00.
        # Thus, the meeting must finish by 10:00 (600 minutes).
        solver.add(start + duration <= 600)
        
    # Carolyn's preference: she would like to avoid meetings on Thursday.
    # We don't rule it out, just treat it as lower preference.
    # (Since we're ordering candidate_days, Thursday is tried after Wednesday.)
    
    # Add busy intervals constraints for Rachel.
    for (busy_start, busy_end) in rachel_busy.get(day, []):
        solver.add(no_overlap(busy_start, busy_end, start))
        
    # Add busy intervals constraints for Carolyn.
    for (busy_start, busy_end) in carolyn_busy.get(day, []):
        solver.add(no_overlap(busy_start, busy_end, start))
        
    # Try each minute in the work hours to find the earliest valid start on this day.
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
    # Format time to HH:MM
    start_hour, start_min = divmod(selected_start, 60)
    end_hour, end_min = divmod(selected_end, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(day_names[selected_day], start_hour, start_min, end_hour, end_min))
else:
    print("No valid meeting time could be found that satisfies all constraints.")