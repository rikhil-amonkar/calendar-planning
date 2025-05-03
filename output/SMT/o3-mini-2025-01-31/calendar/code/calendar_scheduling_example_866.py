from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30  # meeting duration is 30 minutes
WORK_START = 9 * 60    # 9:00 in minutes (540)
WORK_END   = 17 * 60   # 17:00 in minutes (1020)

# Days encoded as: Monday=0, Tuesday=1, Wednesday=2, Thursday=3.
# Peter prefers not to meet on Monday and Thursday, so we'll consider Tuesday and Wednesday.
candidate_days = [1, 2]  # Tuesday and Wednesday

# Catherine's busy schedule (times in minutes from midnight)
catherine_busy = {
    0: [ (9 * 60 + 30, 10 * 60),   # Monday: 9:30 - 10:00 -> [570,600)
         (13 * 60 + 30, 14 * 60) ], # Monday: 13:30 - 14:00 -> [810,840)
    1: [ (11 * 60, 11 * 60 + 30),   # Tuesday: 11:00 - 11:30 -> [660,690)
         (12 * 60 + 30, 14 * 60),   # Tuesday: 12:30 - 14:00 -> [750,840)
         (16 * 60 + 30, 17 * 60) ], # Tuesday: 16:30 - 17:00 -> [990,1020)
    2: [ (16 * 60 + 30, 17 * 60) ], # Wednesday: 16:30 - 17:00 -> [990,1020)
    3: [ (12 * 60 + 30, 13 * 60),   # Thursday: 12:30 - 13:00 -> [750,780)
         (13 * 60 + 30, 14 * 60) ]  # Thursday: 13:30 - 14:00 -> [810,840)
}

# Peter's busy schedule (times in minutes from midnight)
peter_busy = {
    0: [ (9 * 60, 10 * 60 + 30),    # Monday: 9:00 - 10:30 -> [540,630)
         (11 * 60, 11 * 60 + 30),   # Monday: 11:00 - 11:30 -> [660,690)
         (12 * 60, 14 * 60),        # Monday: 12:00 - 14:00 -> [720,840)
         (14 * 60 + 30, 17 * 60) ],  # Monday: 14:30 - 17:00 -> [870,1020)
    1: [ (9 * 60, 17 * 60) ],        # Tuesday: 9:00 - 17:00 -> [540,1020)
    2: [ (9 * 60, 15 * 60 + 30),     # Wednesday: 9:00 - 15:30 -> [540,930)
         (16 * 60, 17 * 60) ],       # Wednesday: 16:00 - 17:00 -> [960,1020)
    3: [ (9 * 60, 12 * 60),          # Thursday: 9:00 - 12:00 -> [540,720)
         (12 * 60 + 30, 16 * 60),    # Thursday: 12:30 - 16:00 -> [750,960)
         (16 * 60 + 30, 17 * 60) ]    # Thursday: 16:30 - 17:00 -> [990,1020)
}

# Helper function: Ensure that the meeting starting at s (lasting duration minutes)
# does not overlap with a busy interval [busy_start, busy_end).
def no_overlap(busy_start, busy_end, s):
    return Or(s + duration <= busy_start, s >= busy_end)

# Function to find the earliest valid meeting time among candidate days.
def find_meeting_time(days):
    for day in days:
        solver = Solver()
        s = Int("s")  # meeting start time in minutes from midnight
        
        # Meeting must be scheduled within work hours.
        solver.add(s >= WORK_START, s + duration <= WORK_END)
        
        # Add Catherine's busy time constraints for the given day.
        for interval in catherine_busy.get(day, []):
            busy_start, busy_end = interval
            solver.add(no_overlap(busy_start, busy_end, s))
        
        # Add Peter's busy time constraints for the given day.
        for interval in peter_busy.get(day, []):
            busy_start, busy_end = interval
            solver.add(no_overlap(busy_start, busy_end, s))
        
        # Check minute-by-minute possibilities within work hours.
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
    start_hour, start_minute = divmod(selected_start, 60)
    end_hour, end_minute = divmod(selected_end, 60)
    # Map day indices back to day names.
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(day_names[selected_day], start_hour, start_minute, end_hour, end_minute))
else:
    print("No valid meeting time could be found that satisfies all constraints.")