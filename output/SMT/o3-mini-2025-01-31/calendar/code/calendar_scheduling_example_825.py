from z3 import Solver, Int, Or, sat

# Meeting duration in minutes
duration = 60

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 9 * 60   # 540
WORK_END   = 17 * 60  # 1020

# Define candidate days: Monday = 0, Tuesday = 1, Wednesday = 2, Thursday = 3.
candidate_days = [0, 1, 2, 3]

# Laura's busy intervals (in minutes) by day:
laura_busy = {
    0: [(10*60+30, 11*60+0), (12*60+30, 13*60+0), (14*60+30, 15*60+30), (16*60+0, 17*60+0)],
    1: [(9*60+30, 10*60+0), (11*60+0, 11*60+30), (13*60+0, 13*60+30), (14*60+30, 15*60+0), (16*60+0, 17*60+0)],
    2: [(11*60+30, 12*60+0), (12*60+30, 13*60+0), (15*60+30, 16*60+30)],
    3: [(10*60+30, 11*60+0), (12*60+0, 13*60+30), (15*60+0, 15*60+30), (16*60+0, 16*60+30)]
}

# Philip's busy intervals (in minutes) by day:
philip_busy = {
    0: [(9*60+0, 17*60+0)],  # Busy whole Monday.
    1: [(9*60+0, 11*60+0), (11*60+30, 12*60+0), (13*60+0, 13*60+30), (14*60+0, 14*60+30), (15*60+0, 16*60+30)],
    2: [(9*60+0, 10*60+0), (11*60+0, 12*60+0), (12*60+30, 16*60+0), (16*60+30, 17*60+0)],
    3: [(9*60+0, 10*60+30), (11*60+0, 12*60+30), (13*60+0, 17*60+0)]
}

solution_found = False
selected_day = None
selected_start = None

# Helper: no overlap between a meeting starting at start_var (lasting 'duration') and a busy interval.
def no_overlap(busy_start, busy_end, start_var):
    # Either the meeting ends before the busy interval starts
    # or it starts after the busy interval ends.
    return Or(start_var + duration <= busy_start, start_var >= busy_end)

# Additional constraint: Philip cannot meet on Wednesday.
# Therefore, if our candidate day is Wednesday (day == 2), we disallow that day.
for day in candidate_days:
    solver = Solver()
    start = Int("start")
    
    # Meeting must be within the work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Disallow Wednesday for Philip.
    if day == 2:
        solver.add(False)
    
    # Add Laura's busy constraints.
    for (busy_start, busy_end) in laura_busy.get(day, []):
        solver.add(no_overlap(busy_start, busy_end, start))
        
    # Add Philip's busy constraints.
    for (busy_start, busy_end) in philip_busy.get(day, []):
        solver.add(no_overlap(busy_start, busy_end, start))
    
    # Search minute-by-minute for a possible start time.
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