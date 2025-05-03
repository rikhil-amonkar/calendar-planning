from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30           # meeting duration in minutes (half an hour)
WORK_START = 9 * 60     # 9:00 -> 540 minutes
WORK_END   = 17 * 60    # 17:00 -> 1020 minutes

# Days encoding: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday.
# Lori cannot meet on Wednesday, so our candidate days are Monday, Tuesday, and Thursday.
candidate_days = [0, 1, 3]

# Jason's busy intervals (in minutes after midnight)
# Monday: 9:00-10:30, 13:00-13:30, 15:00-15:30, 16:00-16:30
# Tuesday: 10:00-15:00
# Wednesday: 9:30-11:00, 11:30-12:00, 12:30-13:00, 13:30-14:00
# Thursday: 10:30-11:00, 12:30-13:00, 14:30-15:00, 15:30-16:00
jason_busy = {
    0: [(9*60, 10*60+30), (13*60, 13*60+30), (15*60, 15*60+30), (16*60, 16*60+30)],
    1: [(10*60, 15*60)],
    2: [(9*60+30, 11*60), (11*60+30, 12*60), (12*60+30, 13*60), (13*60+30, 14*60)],
    3: [(10*60+30, 11*60), (12*60+30, 13*60), (14*60+30, 15*60), (15*60+30, 16*60)]
}

# Lori's busy intervals (in minutes after midnight)
# Monday: 10:30-11:00, 12:00-12:30, 13:30-14:00, 16:00-16:30
# Tuesday: 10:00-12:00, 12:30-14:30, 15:00-17:00
# Wednesday: 9:00-9:30, 10:00-11:00, 13:00-13:30, 14:00-14:30, 15:30-16:30
# Thursday: 9:00-12:00, 12:30-13:30, 15:30-17:00
lori_busy = {
    0: [(10*60+30, 11*60), (12*60, 12*60+30), (13*60+30, 14*60), (16*60, 16*60+30)],
    1: [(10*60, 12*60), (12*60+30, 14*60+30), (15*60, 17*60)],
    2: [(9*60, 9*60+30), (10*60, 11*60), (13*60, 13*60+30), (14*60, 14*60+30), (15*60+30, 16*60+30)],
    3: [(9*60, 12*60), (12*60+30, 13*60+30), (15*60+30, 17*60)]
}

# Utility: A meeting starting at 's' does not conflict with a busy block [busy_start, busy_end)
def no_overlap(busy_start, busy_end, s):
    return Or(s + duration <= busy_start, s >= busy_end)

# Search for the earliest meeting time among candidate days
def find_meeting_time(days):
    for day in days:
        solver = Solver()
        s = Int("s")  # meeting start time (in minutes after midnight)

        # The meeting must be within the work hours.
        solver.add(s >= WORK_START, s + duration <= WORK_END)

        # Add Jason's busy constraints for the day.
        for busy_start, busy_end in jason_busy.get(day, []):
            solver.add(no_overlap(busy_start, busy_end, s))
            
        # Add Lori's busy constraints for the day.
        for busy_start, busy_end in lori_busy.get(day, []):
            solver.add(no_overlap(busy_start, busy_end, s))
        
        # Check every minute from WORK_START to WORK_END - duration for a valid start time.
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