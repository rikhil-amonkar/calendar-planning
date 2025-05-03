from z3 import Solver, Int, Or, sat

# Meeting duration in minutes (30 minutes)
duration = 30

# Work hours in minutes: 9:00 (540) to 17:00 (1020)
WORK_START = 9 * 60    # 540
WORK_END   = 17 * 60   # 1020

# Days encoding: Monday = 0, Tuesday = 1, Wednesday = 2, Thursday = 3.
# Constraints and preferences:
# • Kayla does not want to meet on Wednesday (day 2) so we skip that day.
# • Matthew would like to avoid Tuesday, so we treat it as a lower priority candidate.
# • Matthew would like to avoid meetings on Thursday after 12:00. So if the meeting is on
#   Thursday (day==3), we require that it finishes by 12:00 (i.e. start + duration <= 720).
# We choose candidate days ordering accordingly.
candidate_days = [3, 1]  # Thursday (morning slot), then Tuesday.
# Note: Monday is not available for Matthew (busy all day) and Wednesday is rejected by Kayla.

# Busy intervals for each participant in minutes, per day.
# Times are given as intervals [start, end) with minutes since midnight.
# Kayla's busy schedule:
# Monday: 16:30-17:00 -> (990,1020)
# Tuesday: 10:00-11:00 -> (600,660), 12:00-13:00 -> (720,780), 16:00-16:30 -> (960,990)
# Wednesday: 9:30-10:00 -> (570,600), 11:00-12:30 -> (660,750), 15:00-15:30 -> (900,930)
# Thursday: 10:00-10:30 -> (600,630), 13:00-13:30 -> (780,810), 14:30-15:00 -> (870,900), 16:00-17:00 -> (960,1020)
kayla_busy = {
    0: [(990,1020)],
    1: [(600,660), (720,780), (960,990)],
    2: [(570,600), (660,750), (900,930)],
    3: [(600,630), (780,810), (870,900), (960,1020)]
}

# Matthew's busy schedule:
# Monday: 9:00-17:00 -> (540,1020)
# Tuesday: 9:00-10:30 -> (540,630), 11:00-12:00 -> (660,720), 12:30-14:30 -> (750,870), 15:30-17:00 -> (930,1020)
# Wednesday: 9:00-10:00 -> (540,600), 10:30-15:30 -> (630,930), 16:00-17:00 -> (960,1020)
# Thursday: 9:00-10:00 -> (540,600), 11:30-15:00 -> (690,900), 16:00-16:30 -> (960,990)
matthew_busy = {
    0: [(540,1020)],
    1: [(540,630), (660,720), (750,870), (930,1020)],
    2: [(540,600), (630,930), (960,1020)],
    3: [(540,600), (690,900), (960,990)]
}

solution_found = False
selected_day = None
selected_start = None

# Helper function to ensure a meeting starting at 'start_var' of length duration does NOT overlap 
# with a busy interval given as [busy_start, busy_end).
def no_overlap(busy_start, busy_end, start_var):
    return Or(start_var + duration <= busy_start, start_var >= busy_end)

# Iterate candidate days in preferential order.
for day in candidate_days:
    solver = Solver()
    start = Int("start")
    
    # Meeting must be within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Handle Matthew's Thursday preference: avoid meeting after 12:00.
    if day == 3:
        solver.add(start + duration <= 720)  # finish by 12:00
    
    # Add Kayla's busy intervals for the day.
    for (b_start, b_end) in kayla_busy.get(day, []):
        solver.add(no_overlap(b_start, b_end, start))
    
    # Add Matthew's busy intervals for the day.
    for (b_start, b_end) in matthew_busy.get(day, []):
        solver.add(no_overlap(b_start, b_end, start))
    
    # Loop over each minute in the work day: find the earliest valid start time on this day.
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t)
        if solver.check() == sat:
            selected_start = t
            selected_day = day
            solution_found = True
            solver.pop()  # Remove the last pushed constraint
            break
        solver.pop()
    
    if solution_found:
        break

if solution_found:
    selected_end = selected_start + duration
    # Convert minutes to HH:MM format.
    start_hour, start_min = divmod(selected_start, 60)
    end_hour, end_min = divmod(selected_end, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(day_names[selected_day], start_hour, start_min, end_hour, end_min))
else:
    print("No valid meeting time could be found that satisfies all constraints.")