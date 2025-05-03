from z3 import Solver, Int, Or, sat

# Meeting duration in minutes (60 minutes)
duration = 60

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 9 * 60    # 540 minutes
WORK_END = 17 * 60     # 1020 minutes

# Days encoded as: Monday=0, Tuesday=1, Wednesday=2, Thursday=3.
# Laura cannot meet on Monday or Tuesday, so the candidate days are Wednesday and Thursday.
candidate_days = [2, 3]

# Busy intervals in minutes [start, end) for each participant.
# Times are converted to minutes.
# Laura's busy schedule:
#   Monday: 14:30 to 15:00 -> (870, 900) [but Laura is not available on Monday]
#   Wednesday: 12:00 to 12:30 -> (720, 750)
laura_busy = {
    2: [(720, 750)],
    3: []  # No busy intervals provided for Thursday.
}

# Marie's busy schedule:
#   Monday: 9:00-10:00 -> (540,600), 11:00-15:30 -> (660,930), 16:00-17:00 -> (960,1020)
#   Tuesday: 9:00-9:30 -> (540,570), 11:30-12:00 -> (690,720), 12:30-15:30 -> (750,930), 16:00-16:30 -> (960,990)
#   Wednesday: 9:00-9:30 -> (540,570), 10:30-11:30 -> (630,690), 
#              12:30-14:00 -> (750,840), 14:30-15:00 -> (870,900), 15:30-16:30 -> (930,990)
#   Thursday: 9:00-9:30 -> (540,570), 10:00-11:30 -> (600,690), 12:00-15:30 -> (720,930), 16:00-17:00 -> (960,1020)
marie_busy = {
    0: [(540,600), (660,930), (960,1020)],
    1: [(540,570), (690,720), (750,930), (960,990)],
    2: [(540,570), (630,690), (750,840), (870,900), (930,990)],
    3: [(540,570), (600,690), (720,930), (960,1020)]
}

# Utility function: Given a busy interval [b_start, b_end) and meeting start time s,
# ensure that the meeting (lasting 'duration') does not overlap with that interval.
def no_overlap(b_start, b_end, s):
    # The meeting must either finish before the busy interval starts or start after it ends.
    return Or(s + duration <= b_start, s >= b_end)

solution_found = False
selected_day = None
selected_start = None

# Loop over candidate days in order: Wednesday (2) then Thursday (3).
for day in candidate_days:
    solver = Solver()
    s = Int("s")  # Variable for meeting start time in minutes.
    
    # The meeting must stay within work hours.
    solver.add(s >= WORK_START, s + duration <= WORK_END)
    
    # Add busy constraints from Laura.
    for (b_start, b_end) in laura_busy.get(day, []):
        solver.add(no_overlap(b_start, b_end, s))
    
    # Add busy constraints from Marie.
    for (b_start, b_end) in marie_busy.get(day, []):
        solver.add(no_overlap(b_start, b_end, s))
    
    # Try each minute from WORK_START until the meeting can be scheduled.
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(s == t)
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
    # Convert start and end times from minutes to HH:MM format.
    start_hour, start_minute = divmod(selected_start, 60)
    end_hour, end_minute = divmod(selected_end, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(day_names[selected_day], start_hour, start_minute, end_hour, end_minute))
else:
    print("No valid meeting time could be found that satisfies all constraints.")