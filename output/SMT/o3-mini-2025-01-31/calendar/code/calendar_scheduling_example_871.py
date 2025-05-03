from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30             # meeting duration in minutes
WORK_START = 9 * 60       # 9:00 in minutes (540)
WORK_END   = 17 * 60      # 17:00 in minutes (1020)

# Encode days as: Monday=0, Tuesday=1, Wednesday=2, Thursday=3.
# Anthony would rather not meet on Monday so we consider only Tuesday, Wednesday, and Thursday.
# The group prefers to meet at their earliest availability.
candidate_days = [1, 2, 3]

# Anthony has no meetings.

# Joseph's busy schedule: times are in minutes from midnight
joseph_busy = {
    0: [ (10 * 60 + 30, 11 * 60),       # Monday: 10:30 to 11:00 [630,660)
         (12 * 60 + 30, 13 * 60 + 30),   # Monday: 12:30 to 13:30 [750,810)
         (14 * 60, 15 * 60) ],           # Monday: 14:00 to 15:00 [840,900)
    1: [ (9 * 60, 10 * 60),             # Tuesday: 9:00 to 10:00 [540,600)
         (10 * 60 + 30, 12 * 60 + 30),   # Tuesday: 10:30 to 12:30 [630,750)
         (13 * 60, 14 * 60),             # Tuesday: 13:00 to 14:00 [780,840)
         (14 * 60 + 30, 16 * 60),         # Tuesday: 14:30 to 16:00 [870,960)
         (16 * 60 + 30, 17 * 60) ],       # Tuesday: 16:30 to 17:00 [990,1020)
    2: [ (9 * 60, 9 * 60 + 30),          # Wednesday: 9:00 to 9:30 [540,570)
         (10 * 60, 11 * 60 + 30),         # Wednesday: 10:00 to 11:30 [600,690)
         (13 * 60, 16 * 60),              # Wednesday: 13:00 to 16:00 [780,960)
         (16 * 60 + 30, 17 * 60) ],       # Wednesday: 16:30 to 17:00 [990,1020)
    3: [ (9 * 60, 9 * 60 + 30),          # Thursday: 9:00 to 9:30 [540,570)
         (10 * 60, 10 * 60 + 30),         # Thursday: 10:00 to 10:30 [600,630)
         (11 * 60, 11 * 60 + 30),         # Thursday: 11:00 to 11:30 [660,690)
         (12 * 60, 12 * 60 + 30),         # Thursday: 12:00 to 12:30 [720,750)
         (13 * 60, 13 * 60 + 30),         # Thursday: 13:00 to 13:30 [780,810)
         (14 * 60, 15 * 60),              # Thursday: 14:00 to 15:00 [840,900)
         (16 * 60 + 30, 17 * 60) ],       # Thursday: 16:30 to 17:00 [990,1020)
}

# Utility function to ensure that meeting starting at 's' (lasting for 'duration' minutes)
# does not overlap a busy interval [busy_start, busy_end).
def no_overlap(busy_start, busy_end, s):
    return Or(s + duration <= busy_start, s >= busy_end)

# Function to find an available meeting time given candidate days.
# We search each candidate day in order and for each day we try all minutes starting from WORK_START.
def find_meeting_time(days):
    for day in days:
        solver = Solver()
        # Define meeting start-time variable (in minutes from midnight)
        s = Int("s")
        solver.add(s >= WORK_START, s + duration <= WORK_END)
        
        # Anthony has no meetings, so no constraints from him.
        
        # Add Joseph's busy interval constraints for the day.
        for interval in joseph_busy.get(day, []):
            busy_start, busy_end = interval
            solver.add(no_overlap(busy_start, busy_end, s))
        
        # Search for the earliest meeting time on this day.
        search_start = WORK_START
        search_end = WORK_END - duration + 1  # inclusive range for start time
        
        for t in range(search_start, search_end):
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