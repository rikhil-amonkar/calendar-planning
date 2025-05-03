from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30           # meeting duration in minutes (half an hour)
WORK_START = 9 * 60     # 9:00 -> 540 minutes
WORK_END   = 17 * 60    # 17:00 -> 1020 minutes

# Days encoding: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday.
# Debra cannot meet on Tuesday, so our candidate days are Monday, Wednesday, and Thursday.
candidate_days = [0, 2, 3]

# Elijah's busy time intervals (in minutes after midnight)
# Monday: 11:00-13:00
# Tuesday: 9:00-10:00, 14:00-15:30, 16:00-16:30
# Wednesday: 9:00-10:00, 10:30-11:00, 12:00-12:30, 15:30-16:00, 16:30-17:00
# Thursday: 9:00-9:30, 10:00-10:30, 14:30-15:30
elijah_busy = {
    0: [(11*60, 13*60)],  # Monday: (660, 780)
    1: [(9*60, 10*60), (14*60, 15*60+30), (16*60, 16*60+30)],  # Tuesday
    2: [(9*60, 10*60), (10*60+30, 11*60), (12*60, 12*60+30), (15*60+30, 16*60), (16*60+30, 17*60)],  # Wednesday
    3: [(9*60, 9*60+30), (10*60, 10*60+30), (14*60+30, 15*60+30)]  # Thursday
}

# Debra's busy time intervals (in minutes after midnight)
# Monday: 9:00-9:30, 10:30-11:00, 11:30-17:00
# Tuesday: 9:00-15:30, 16:00-17:00
# Wednesday: 9:00-17:00
# Thursday: 9:00-10:30, 11:00-14:30, 15:00-15:30, 16:00-16:30
debra_busy = {
    0: [(9*60, 9*60+30), (10*60+30, 11*60), (11*60+30, 17*60)],  # Monday
    1: [(9*60, 15*60+30), (16*60, 17*60)],  # Tuesday (but Debra cannot meet on Tuesday)
    2: [(9*60, 17*60)],  # Wednesday
    3: [(9*60, 10*60+30), (11*60, 14*60+30), (15*60, 15*60+30), (16*60, 16*60+30)]  # Thursday
}

# Utility: returns a Z3 constraint ensuring that the meeting starting at 's'
# does not overlap with the busy interval [busy_start, busy_end).
def no_overlap(busy_start, busy_end, s):
    return Or(s + duration <= busy_start, s >= busy_end)

# Find the earliest meeting time among the candidate days.
# For each candidate day, we iterate minute by minute (from WORK_START to WORK_END - duration),
# and check if a meeting starting at that time satisfies all constraints.
def find_meeting_time(days):
    for day in days:
        solver = Solver()
        s = Int("s")  # meeting start time in minutes after midnight
        
        # Ensure the meeting fits in the work hours.
        solver.add(s >= WORK_START, s + duration <= WORK_END)
        
        # Add Elijah's constraints for the day.
        for busy_start, busy_end in elijah_busy.get(day, []):
            solver.add(no_overlap(busy_start, busy_end, s))
        
        # Add Debra's constraints for the day.
        for busy_start, busy_end in debra_busy.get(day, []):
            solver.add(no_overlap(busy_start, busy_end, s))
        
        # Try every possible starting minute in ascending order to get the earliest availability.
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