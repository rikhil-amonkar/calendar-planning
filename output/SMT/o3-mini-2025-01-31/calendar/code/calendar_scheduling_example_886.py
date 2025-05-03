from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 60           # meeting duration in minutes (one hour)
WORK_START = 9 * 60     # 9:00 -> 540 minutes
WORK_END   = 17 * 60    # 17:00 -> 1020 minutes

# Days encoding: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday.
# Although the task allows Monday, Tuesday, Wednesday, or Thursday,
# Robert is busy all day on Tuesday, so we remove it.
candidate_days = [0, 2, 3]

# Busy intervals in minutes after midnight

# Jesse's busy intervals:
# Monday: 9:30-10:00        => (570, 600)
# Tuesday: 9:00-10:00, 13:30-14:00, 15:30-16:00, 16:30-17:00
#          -> (540,600), (810,840), (930,960), (990,1020)
# Wednesday: 11:30-12:30, 13:00-13:30, 15:30-16:00  => (690,750), (780,810), (930,960)
# Thursday: 12:00-12:30, 13:00-13:30, 14:00-14:30, 15:30-16:00
#          -> (720,750), (780,810), (840,870), (930,960)
jesse_busy = {
    0: [(9*60+30, 10*60)],  # Monday
    1: [(9*60, 10*60), (13*60+30, 14*60), (15*60+30, 16*60), (16*60+30, 17*60)],  # Tuesday
    2: [(11*60+30, 12*60+30), (13*60, 13*60+30), (15*60+30, 16*60)],  # Wednesday
    3: [(12*60, 12*60+30), (13*60, 13*60+30), (14*60, 14*60+30), (15*60+30, 16*60)]  # Thursday
}

# Robert's busy intervals:
# Monday: 10:00-11:00, 12:00-13:30, 14:00-14:30, 15:00-16:00
#         -> (600,660), (720,810), (840,870), (900,960)
# Tuesday: 9:00-17:00          -> (540,1020)
# Wednesday: 9:00-13:30, 14:00-17:00
#            -> (540,810), (840,1020)
# Thursday: 9:30-11:00, 11:30-15:00, 15:30-17:00
#           -> (570,660), (690,900), (930,1020)
robert_busy = {
    0: [(10*60, 11*60), (12*60, 13*60+30), (14*60, 14*60+30), (15*60, 16*60)],
    1: [(9*60, 17*60)],
    2: [(9*60, 13*60+30), (14*60, 17*60)],
    3: [(9*60+30, 11*60), (11*60+30, 15*60), (15*60+30, 17*60)]
}

# Additional constraint: Jesse can not meet on Monday before 12:00.
# For Monday (day 0) meeting, the meeting must start at or after 12:00 (720 minutes).
MONDAY_START_LIMIT = 12 * 60  # 720 minutes

# Utility: define non-overlap for a busy block [busy_start, busy_end):
def no_overlap(busy_start, busy_end, s):
    return Or(s + duration <= busy_start, s >= busy_end)

# Function to search for the earliest valid meeting time in candidate days, minute by minute.
def find_meeting_time(days):
    for day in days:
        solver = Solver()
        s = Int("s")  # meeting start time in minutes after midnight
        
        # Meeting must be within work hours.
        solver.add(s >= WORK_START, s + duration <= WORK_END)
        
        # Apply additional Monday constraint for Jesse.
        if day == 0:
            solver.add(s >= MONDAY_START_LIMIT)
        
        # Add Jesse's busy constraints for current day.
        for busy_start, busy_end in jesse_busy.get(day, []):
            solver.add(no_overlap(busy_start, busy_end, s))
        
        # Add Robert's busy constraints for current day.
        for busy_start, busy_end in robert_busy.get(day, []):
            solver.add(no_overlap(busy_start, busy_end, s))
        
        # Search minute-by-minute for a valid start time.
        for t in range(WORK_START, WORK_END - duration + 1):
            solver.push()
            solver.add(s == t)
            if solver.check() == sat:
                return day, t
            solver.pop()
    return None, None

selected_day, selected_start = find_meeting_time(candidate_days)

if selected_day is not None:
    selected_end = selected_start + duration
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
    start_hour, start_minute = divmod(selected_start, 60)
    end_hour, end_minute = divmod(selected_end, 60)
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(day_names[selected_day], start_hour, start_minute, end_hour, end_minute))
else:
    print("No valid meeting time could be found that satisfies all constraints.")