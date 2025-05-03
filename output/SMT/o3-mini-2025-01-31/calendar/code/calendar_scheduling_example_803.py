from z3 import Solver, Int, Or, sat

# Meeting duration is 60 minutes.
duration = 60

# Work hours in minutes from midnight: 9:00 is 540, 17:00 is 1020.
WORK_START = 9 * 60
WORK_END = 17 * 60

# We will use an integer 'start' for the meeting start time (in minutes from midnight)
start = Int("start")

# Days are coded as: Monday=0, Tuesday=1, Wednesday=2, Thursday=3.
# Allowed days by the task are Monday, Tuesday, Wednesday, or Thursday.
# Additional constraints:
#   - Elijah cannot meet on Tuesday (day 1 is disallowed for him).
#   - Gary does not want to meet on Monday before 11:30. (11:30 = 690 minutes)
#   - Gary does not want to meet on Thursday.
#
# Hence, the only candidate days that satisfy both participants are Monday and Wednesday.
candidate_days = [0, 2]  # 0: Monday, 2: Wednesday

# Busy schedules for Elijah (each tuple is (busy_start, busy_end) in minutes):
# Monday: 9:00-9:30, 11:30-12:00, 15:30-16:30
# Tuesday: 13:00-13:30, 15:30-16:00
# Wednesday: 10:30-11:30, 14:00-14:30, 15:00-15:30, 16:00-16:30
# Thursday: 11:00-11:30, 13:30-14:00, 14:30-15:00
elijah_busy = {
    0: [(540,570), (690,720), (930,990)],
    1: [(780,810), (930,960)],
    2: [(630,690), (840,870), (900,930), (960,990)],
    3: [(660,690), (810,840), (870,900)]
}

# Busy schedules for Gary:
# Monday: 12:00-12:30, 13:00-13:30, 14:30-15:30, 16:00-16:30
# Tuesday: 10:30-11:00, 12:00-13:30, 14:00-15:00, 15:30-17:00
# Wednesday: 9:30-10:00, 11:30-15:00, 15:30-16:00, 16:30-17:00
# Thursday: 9:00-9:30, 10:00-12:30, 14:00-15:30, 16:00-16:30
gary_busy = {
    0: [(720,750), (780,810), (870,930), (960,990)],
    1: [(630,660), (720,810), (840,900), (930,1020)],
    2: [(570,600), (690,900), (930,960), (990,1020)],
    3: [(540,570), (600,750), (840,930), (960,990)]
}

# Helper function: returns a condition that the meeting interval [start, start+duration)
# does not overlap with a busy interval [busy_start, busy_end).
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

solution_found = False
selected_day = None
selected_start = None

# Iterate over candidate days in order.
for day in candidate_days:
    solver = Solver()
    
    # Meeting must be within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Day-specific constraints:
    # Elijah cannot meet on Tuesday. (Our candidate_days already exclude Tuesday.)
    # Gary does not want to meet on Monday before 11:30.
    if day == 0:
        solver.add(start >= 11 * 60 + 30)  # 11:30 -> 690 minutes
    # Gary does not want to meet on Thursday.
    if day == 3:
        # If Thursday were considered, we would disallow it.
        solver.add(False)
    
    # Add Elijah's busy intervals for this day.
    for interval in elijah_busy.get(day, []):
        b_start, b_end = interval
        solver.add(non_overlap(b_start, b_end))
    
    # Add Gary's busy intervals for this day.
    for interval in gary_busy.get(day, []):
        b_start, b_end = interval
        solver.add(non_overlap(b_start, b_end))
    
    # Search for the earliest possible meeting start time (minute by minute).
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t)
        if solver.check() == sat:
            selected_start = t
            selected_day = day
            solution_found = True
            solver.pop()  # Remove the push before breaking.
            break
        solver.pop()
    
    if solution_found:
        break

if solution_found:
    selected_end = selected_start + duration
    # Convert minutes to hour:minute format.
    start_hour, start_min = divmod(selected_start, 60)
    end_hour, end_min = divmod(selected_end, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(day_names[selected_day], start_hour, start_min, end_hour, end_min))
else:
    print("No valid meeting time could be found that satisfies all constraints.")