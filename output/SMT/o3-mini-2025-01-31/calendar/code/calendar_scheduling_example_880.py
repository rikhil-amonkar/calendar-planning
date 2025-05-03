from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 60           # meeting duration in minutes (one hour)
WORK_START = 9 * 60     # 9:00 in minutes (540)
WORK_END   = 17 * 60    # 17:00 in minutes (1020)

# We encode days as: Monday=0, Tuesday=1, Wednesday=2, Thursday=3.
# Billy would like to avoid more meetings on Wednesday, so we first try days other than Wednesday.
candidate_days = [0, 1, 3]

# Busy schedules in minutes from midnight.

# Anna's busy schedule:
# Monday: 10:00-10:30, 14:00-15:00
# Tuesday: 9:30-10:00, 14:00-15:00, 16:30-17:00
# Wednesday: 9:30-10:30, 13:30-14:00
# Thursday: 9:30-10:00, 11:30-12:00, 13:30-14:00, 16:30-17:00
anna_busy = {
    0: [(10 * 60, 10 * 60 + 30), (14 * 60, 15 * 60)],
    1: [(9 * 60 + 30, 10 * 60), (14 * 60, 15 * 60), (16 * 60 + 30, 17 * 60)],
    2: [(9 * 60 + 30, 10 * 60 + 30), (13 * 60 + 30, 14 * 60)],
    3: [(9 * 60 + 30, 10 * 60), (11 * 60 + 30, 12 * 60), (13 * 60 + 30, 14 * 60), (16 * 60 + 30, 17 * 60)]
}

# Billy's busy schedule:
# Monday: 9:00-10:30, 11:00-15:30, 16:00-16:30
# Tuesday: 9:00-17:00
# Wednesday: 9:00-13:30, 14:00-14:30, 15:30-17:00
# Thursday: 9:00-14:30, 16:00-16:30
billy_busy = {
    0: [(9 * 60, 10 * 60 + 30), (11 * 60, 15 * 60 + 30), (16 * 60, 16 * 60 + 30)],
    1: [(9 * 60, 17 * 60)],  # Fully busy on Tuesday
    2: [(9 * 60, 13 * 60 + 30), (14 * 60, 14 * 60 + 30), (15 * 60 + 30, 17 * 60)],
    3: [(9 * 60, 14 * 60 + 30), (16 * 60, 16 * 60 + 30)]
}

# Utility function: For a meeting starting at time 's' (with given duration),
# ensure that it does not overlap a busy interval [busy_start, busy_end).
def no_overlap(busy_start, busy_end, s):
    # There is no overlap if meeting ends at or before busy_start or starts at or after busy_end.
    return Or(s + duration <= busy_start, s >= busy_end)

# Try to find a meeting time on the given candidate days in order
def find_meeting_time(days):
    for day in days:
        solver = Solver()
        s = Int("s")  # s is meeting start time in minutes from midnight
        
        # Meeting must be scheduled within working hours.
        solver.add(s >= WORK_START, s + duration <= WORK_END)
        
        # Add Anna's busy constraints for the given day.
        for busy_start, busy_end in anna_busy.get(day, []):
            solver.add(no_overlap(busy_start, busy_end, s))
            
        # Add Billy's busy constraints for the given day.
        for busy_start, busy_end in billy_busy.get(day, []):
            solver.add(no_overlap(busy_start, busy_end, s))
        
        # Search for the earliest possible meeting time, minute by minute.
        for t in range(WORK_START, WORK_END - duration + 1):
            solver.push()
            solver.add(s == t)
            if solver.check() == sat:
                return day, t
            solver.pop()
    return None, None

selected_day, selected_start = find_meeting_time(candidate_days)

# If no meeting could be found on candidate days, as a fallback, try Wednesday.
if selected_day is None:
    # Wednesday is encoded as day 2.
    candidate_days = [2]
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