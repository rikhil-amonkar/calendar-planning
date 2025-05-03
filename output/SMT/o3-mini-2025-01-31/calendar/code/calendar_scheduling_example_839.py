from z3 import Solver, Int, Or, sat

# Meeting duration for Alan and Shirley in minutes (60 minutes)
duration = 60

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 9 * 60      # 540 minutes
WORK_END = 17 * 60       # 1020 minutes

# Days encoded as: Monday=0, Tuesday=1, Wednesday=2, Thursday=3.
# We check days in order for the group's earliest availability.
candidate_days = [0, 1, 2, 3]

# Define the busy intervals for each participant.
# Each interval is a tuple (start, end) in minutes.
# Alan's busy schedule:
# Monday: 9:00-9:30, 11:00-11:30, 12:00-12:30, 13:00-13:30, 14:00-14:30, 15:30-16:30
# Tuesday: 9:00-10:00, 11:30-12:00, 13:00-16:00
# Wednesday: 9:30-10:00, 15:30-16:00, 16:30-17:00
# Thursday: 9:00-10:00, 11:00-11:30, 12:00-13:30, 14:00-15:30
alan_busy = {
    0: [(540,570), (660,690), (720,750), (780,810), (840,870), (930,990)],
    1: [(540,600), (690,720), (780,960)],
    2: [(570,600), (930,960), (990,1020)],
    3: [(540,600), (660,690), (720,810), (840,930)]
}

# Shirley's busy schedule:
# Monday: 9:00-10:00, 11:30-13:30, 14:00-15:00, 16:00-17:00
# Tuesday: 9:00-10:00, 11:00-13:00, 13:30-14:30, 15:00-15:30, 16:30-17:00
# Wednesday: 10:00-11:00, 12:30-13:30, 14:00-14:30
# Thursday: 9:00-10:30, 11:00-11:30, 12:00-14:00, 14:30-17:00
shirley_busy = {
    0: [(540,600), (690,810), (840,900), (960,1020)],
    1: [(540,600), (660,780), (810,870), (900,930), (990,1020)],
    2: [(600,660), (750,810), (840,870)],
    3: [(540,630), (660,690), (720,840), (870,1020)]
}

# Utility function to enforce a meeting starting at time s (with given duration)
# does not overlap with a busy interval [b_start, b_end).
def no_overlap(b_start, b_end, s):
    return Or(s + duration <= b_start, s >= b_end)

solution_found = False
selected_day = None
selected_start = None

# Iterate through candidate days in order (earliest first).
for day in candidate_days:
    solver = Solver()
    s = Int("s")  # meeting start time variable in minutes
    
    # The meeting must be within work hours (ensuring the full duration fits).
    solver.add(s >= WORK_START, s + duration <= WORK_END)
    
    # Add constraints for Alan's busy intervals on current day.
    for (b_start, b_end) in alan_busy.get(day, []):
        solver.add(no_overlap(b_start, b_end, s))
    
    # Add constraints for Shirley's busy intervals on current day.
    for (b_start, b_end) in shirley_busy.get(day, []):
        solver.add(no_overlap(b_start, b_end, s))
    
    # Try each possible minute within work hours.
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
    # Convert minutes to HH:MM format
    start_hour, start_minute = divmod(selected_start, 60)
    end_hour, end_minute = divmod(selected_end, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(day_names[selected_day], start_hour, start_minute, end_hour, end_minute))
else:
    print("No valid meeting time could be found that satisfies all constraints.")