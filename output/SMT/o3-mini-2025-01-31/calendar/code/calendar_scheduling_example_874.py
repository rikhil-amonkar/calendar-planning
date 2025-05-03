from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 60            # meeting duration in minutes (1 hour)
WORK_START = 9 * 60      # 9:00 in minutes (540)
WORK_END   = 17 * 60     # 17:00 in minutes (1020)

# We encode days as: Monday=0, Tuesday=1, Wednesday=2, Thursday=3.
# Samuel does not want to meet on Tuesday, so his candidate days are: Monday, Wednesday, Thursday.
# Kimberly would rather not meet on Wednesday after 12:30.
# For a 1-hour meeting on Wednesday to avoid being "after 12:30", the meeting must finish by 12:30,
# i.e., the meeting start time s must satisfy s + 60 <= 12:30 (750 minutes) ⇒ s <= 690.
candidate_days = [0, 2, 3]

# Define busy schedules (times are in minutes from midnight).
# Samuel's schedule:
samuel_busy = {
    0: [ (10 * 60 + 30, 11 * 60 + 30),  # Monday: 10:30 - 11:30
         (12 * 60 + 30, 13 * 60 + 30),  # Monday: 12:30 - 13:30
         (15 * 60, 15 * 60 + 30) ],     # Monday: 15:00 - 15:30
    # Tuesday is excluded due to preference.
    2: [ (14 * 60, 14 * 60 + 30),        # Wednesday: 14:00 - 14:30
         (16 * 60, 16 * 60 + 30) ],      # Wednesday: 16:00 - 16:30
    3: [ (11 * 60 + 30, 12 * 60),         # Thursday: 11:30 - 12:00
         (12 * 60 + 30, 13 * 60),         # Thursday: 12:30 - 13:00
         (15 * 60, 15 * 60 + 30),         # Thursday: 15:00 - 15:30
         (16 * 60, 16 * 60 + 30) ],       # Thursday: 16:00 - 16:30
}

# Kimberly's schedule:
kimberly_busy = {
    0: [ (9 * 60 + 30, 10 * 60 + 30),   # Monday: 9:30 - 10:30
         (11 * 60 + 30, 13 * 60 + 30),  # Monday: 11:30 - 13:30
         (14 * 60, 14 * 60 + 30),       # Monday: 14:00 - 14:30
         (15 * 60, 16 * 60 + 30) ],     # Monday: 15:00 - 16:30
    1: [ (9 * 60, 9 * 60 + 30),         # Tuesday: 9:00 - 9:30
         (10 * 60, 13 * 60 + 30),        # Tuesday: 10:00 - 13:30
         (14 * 60, 14 * 60 + 30),        # Tuesday: 14:00 - 14:30
         (15 * 60 + 30, 17 * 60) ],      # Tuesday: 15:30 - 17:00
    2: [ (9 * 60 + 30, 11 * 60 + 30),    # Wednesday: 9:30 - 11:30
         (12 * 60 + 30, 13 * 60),        # Wednesday: 12:30 - 13:00
         (13 * 60 + 30, 14 * 60),        # Wednesday: 13:30 - 14:00
         (16 * 60, 17 * 60) ],           # Wednesday: 16:00 - 17:00
    3: [ (9 * 60, 10 * 60),             # Thursday: 9:00 - 10:00
         (10 * 60 + 30, 12 * 60 + 30),   # Thursday: 10:30 - 12:30
         (13 * 60, 17 * 60) ],           # Thursday: 13:00 - 17:00
}

# Utility function: For a meeting start time 's' (lasting for 'duration'),
# ensure that it does not overlap a busy interval defined by [busy_start, busy_end).
def no_overlap(busy_start, busy_end, s):
    return Or(s + duration <= busy_start, s >= busy_end)

# Function to search for a meeting time on one of the candidate days.
def find_meeting_time(days):
    for day in days:
        solver = Solver()
        # Define the meeting start time variable (in minutes from midnight)
        s = Int("s")
        solver.add(s >= WORK_START, s + duration <= WORK_END)
        
        # Add busy constraints for Samuel on this day
        for interval in samuel_busy.get(day, []):
            busy_start, busy_end = interval
            solver.add(no_overlap(busy_start, busy_end, s))
        
        # Add busy constraints for Kimberly on this day
        for interval in kimberly_busy.get(day, []):
            busy_start, busy_end = interval
            solver.add(no_overlap(busy_start, busy_end, s))
        
        # If the day is Wednesday (day==2), Kimberly prefers not to meet after 12:30.
        # For a one-hour meeting, we ensure that the meeting finishes by 12:30 (750 minutes)
        # which means s + 60 <= 750, or s <= 690.
        if day == 2:
            solver.add(s <= 690)
        
        # Try every possible start minute to find the earliest available meeting time.
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
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}.".
          format(day_names[selected_day], start_hour, start_minute, end_hour, end_minute))
else:
    print("No valid meeting time could be found that satisfies all constraints.")