from z3 import Solver, Int, Or, sat

# Meeting duration: 30 minutes
duration = 30

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 9 * 60
WORK_END = 17 * 60

# Define the meeting start time variable (in minutes from midnight)
start = Int("start")

# Candidate days: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday.
# Extra constraints:
# • Joshua does not want to meet on Tuesday before 13:00.
# • Donald cannot meet on Monday and on Thursday.
# 
# Thus, the overall days available (from both participants) are Tuesday and Wednesday.
candidate_days = [1, 2]

# Busy schedules in minutes
# Joshua's busy schedule:
# Monday (0):
#   11:00-11:30 -> (660,690)
#   13:00-13:30 -> (780,810)
#   15:30-16:00 -> (930,960)
# Tuesday (1):
#   12:30-13:30 -> (750,810)
# Wednesday (2):
#   12:30-13:00 -> (750,780)
# Thursday (3):
#   11:30-12:00 -> (690,720)
#   15:00-15:30 -> (900,930)
joshua_busy = {
    0: [(660, 690), (780, 810), (930, 960)],
    1: [(750, 810)],
    2: [(750, 780)],
    3: [(690, 720), (900, 930)]
}

# Donald's busy schedule:
# Monday (0):
#   9:00-9:30 ->  (540,570)
#   10:00-11:30 -> (600,690)
#   12:00-13:00 -> (720,780)
#   13:30-14:00 -> (810,840)
#   15:00-17:00 -> (900,1020)
# Tuesday (1):
#   9:00-10:30 -> (540,630)
#   12:30-14:30 -> (750,870)
#   16:30-17:00 -> (990,1020)
# Wednesday (2):
#   10:30-11:30 -> (630,690)
#   12:00-12:30 -> (720,750)
#   14:00-14:30 -> (840,870)
#   15:30-16:00 -> (930,960)
# Thursday (3):
#   9:00-9:30 ->   (540,570)
#   10:00-11:30 -> (600,690)
#   12:00-12:30 -> (720,750)
#   13:00-14:00 -> (780,840)
#   15:30-17:00 -> (930,1020)
donald_busy = {
    0: [(540,570), (600,690), (720,780), (810,840), (900,1020)],
    1: [(540,630), (750,870), (990,1020)],
    2: [(630,690), (720,750), (840,870), (930,960)],
    3: [(540,570), (600,690), (720,750), (780,840), (930,1020)]
}

# Helper: ensure meeting interval [start, start+duration) does not overlap [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

solution_found = False
selected_day = None
selected_start = None

# Loop over candidate days in order (Tuesday then Wednesday)
for day in candidate_days:
    solver = Solver()
    # Meeting must be within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add busy constraints for Joshua for the given day.
    for (b_start, b_end) in joshua_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Add busy constraints for Donald for the given day.
    for (b_start, b_end) in donald_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Add Joshua's extra preference: if meeting is on Tuesday (day == 1), start must be >= 13:00 (780)
    if day == 1:
        solver.add(start >= 13 * 60)  # 780 minutes
    
    # No additional time restrictions for Wednesday (day == 2).
    
    # Search for the earliest minute on this day that works.
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
    start_hr, start_min = divmod(selected_start, 60)
    end_hr, end_min = divmod(selected_end, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(day_names[selected_day], start_hr, start_min, end_hr, end_min))
else:
    print("No valid meeting time could be found that satisfies all constraints.")