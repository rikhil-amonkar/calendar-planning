from z3 import Solver, Int, Or, sat

# Meeting duration: 60 minutes.
duration = 60

# Work hours in minutes from midnight: 9:00 (540) to 17:00 (1020)
WORK_START = 9 * 60   # 540
WORK_END   = 17 * 60  # 1020

# Candidate days represented as integers:
# Monday = 0, Tuesday = 1, Wednesday = 2, Thursday = 3.
candidate_days = [0, 1, 2, 3]

# Natalie has no meetings, so no busy intervals.
natalie_busy = {
    0: [],
    1: [],
    2: [],
    3: []
}

# Christian's busy schedule (in minutes):
# Monday: 9:00-9:30 -> (540,570); 10:00-14:30 -> (600,870); 15:00-16:00 -> (900,960); 16:30-17:00 -> (990,1020)
# Tuesday: 9:30-14:30 -> (570,870); 15:30-17:00 -> (930,1020)
# Wednesday: 9:30-10:00 -> (570,600); 10:30-16:30 -> (630,990)
# Thursday: 9:00-9:30 -> (540,570); 10:00-10:30 -> (600,630); 11:00-11:30 -> (660,690);
#           12:00-12:30 -> (720,750); 13:30-14:30 -> (810,870); 15:30-17:00 -> (930,1020)
christian_busy = {
    0: [(540,570), (600,870), (900,960), (990,1020)],
    1: [(570,870), (930,1020)],
    2: [(570,600), (630,990)],
    3: [(540,570), (600,630), (660,690), (720,750), (810,870), (930,1020)]
}

solution_found = False
selected_day = None
selected_start = None

# Helper function: ensures that a one-hour meeting starting at start_var does not overlap
# a busy interval [busy_start, busy_end)
def no_overlap(busy_start, busy_end, start_var):
    return Or(start_var + duration <= busy_start, start_var >= busy_end)

# The preferences from the participants:
# - Natalie would like to avoid more meetings on Tuesday -> disallow Tuesday (day == 1).
# - Christian would like to avoid more meetings on Thursday after 13:30.
#   Given the meeting lasts 1 hour, if scheduled on Thursday (day == 3)
#   it must end by 13:30 (810 minutes), that is start + duration <= 810.
# - The meeting must start as early as possible subject to everyone’s schedules.
for day in candidate_days:
    solver = Solver()
    start = Int("start")
    
    # Meeting must be within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Apply participant preferences:
    # Natalie wants to avoid Tuesday.
    if day == 1:
        solver.add(False)  # Disqualify Tuesday.
    
    # Christian prefers not to have meetings on Thursday after 13:30.
    # For a meeting on Thursday, force the meeting to finish by 13:30, i.e.
    # start + duration <= 13:30 which is 810 minutes.
    if day == 3:
        solver.add(start + duration <= 13 * 60 + 30)  # start + 60 <= 810

    # Add constraints to avoid busy intervals for Natalie.
    for (busy_start, busy_end) in natalie_busy.get(day, []):
        solver.add(no_overlap(busy_start, busy_end, start))
    
    # Add constraints to avoid busy intervals for Christian.
    for (busy_start, busy_end) in christian_busy.get(day, []):
        solver.add(no_overlap(busy_start, busy_end, start))
    
    # Search for an available start time (minute-by-minute) for the current day.
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
    start_hour, start_min = divmod(selected_start, 60)
    end_hour, end_min = divmod(selected_end, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(day_names[selected_day], start_hour, start_min, end_hour, end_min))
else:
    print("No valid meeting time could be found that satisfies all constraints.")