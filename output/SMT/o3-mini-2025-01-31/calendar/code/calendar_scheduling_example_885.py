from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 60           # meeting duration in minutes (one hour)
WORK_START = 9 * 60     # 9:00 → 540 minutes
WORK_END   = 17 * 60    # 17:00 → 1020 minutes

# Days encoding: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday.
# Due to constraints ("Jerry can not meet on Thursday") and the additional restriction for Monday,
# our candidate days are Monday, Tuesday, and Wednesday.
candidate_days = [0, 1, 2]

# Jerry's busy intervals (in minutes after midnight)
# Monday (day 0): 11:00-11:30, 12:00-12:30, 13:00-13:30, 14:30-15:30
# Tuesday (day 1): 9:00-11:00, 11:30-12:30, 13:00-14:00, 14:30-15:00, 15:30-17:00
# Wednesday (day 2): 9:00-16:30
jerry_busy = {
    0: [(11*60, 11*60+30), (12*60, 12*60+30), (13*60, 13*60+30), (14*60+30, 15*60+30)],
    1: [(9*60, 11*60), (11*60+30, 12*60+30), (13*60, 14*60), (14*60+30, 15*60), (15*60+30, 17*60)],
    2: [(9*60, 16*60+30)]
}

# Jesse has no meetings, so there are no busy intervals for Jesse.

# Additional constraint: On Monday, Jerry cannot meet after 15:30.
# That means any meeting on Monday must end by 15:30.
MONDAY_MEETING_END_LIMIT = 15 * 60 + 30  # 15:30 in minutes (930 minutes)

# Utility function ensuring that a meeting starting at 's' does not overlap with a busy block [busy_start, busy_end).
def no_overlap(busy_start, busy_end, s):
    return Or(s + duration <= busy_start, s >= busy_end)

# Search for the earliest meeting time over candidate days.
def find_meeting_time(days):
    for day in days:
        solver = Solver()
        s = Int("s")  # meeting start time in minutes after midnight

        # Meeting must be within work hours.
        solver.add(s >= WORK_START, s + duration <= WORK_END)

        # If it is Monday, add the extra constraint that the meeting must end by 15:30.
        if day == 0:
            solver.add(s + duration <= MONDAY_MEETING_END_LIMIT)
        
        # Add Jerry's busy constraints for the day.
        for busy_start, busy_end in jerry_busy.get(day, []):
            solver.add(no_overlap(busy_start, busy_end, s))
        
        # Since Jesse is free, we don't need to add any constraints for him.

        # Check for a valid start time, scanning minute-by-minute from WORK_START.
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