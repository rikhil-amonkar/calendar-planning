from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 60            # meeting duration in minutes (1 hour)
WORK_START = 9 * 60      # 9:00 in minutes (540)
WORK_END   = 17 * 60     # 17:00 in minutes (1020)

# Encode days as: Monday=0, Tuesday=1, Wednesday=2, Thursday=3.
# Deborah has no meetings.
# John's busy schedule (times in minutes from midnight):
john_busy = {
    0: [ (9 * 60, 15 * 60),      # Monday: 9:00 to 15:00 [540,900)
         (15 * 60 + 30, 17 * 60) ], # Monday: 15:30 to 17:00 [930,1020)
    1: [ (9 * 60, 13 * 60 + 30),   # Tuesday: 9:00 to 13:30 [540,810)
         (14 * 60, 15 * 60 + 30),   # Tuesday: 14:00 to 15:30 [840,930)
         (16 * 60, 17 * 60) ],      # Tuesday: 16:00 to 17:00 [960,1020)
    2: [ (9 * 60, 11 * 60),       # Wednesday: 9:00 to 11:00 [540,660)
         (11 * 60 + 30, 12 * 60),  # Wednesday: 11:30 to 12:00 [690,720)
         (13 * 60 + 30, 16 * 60),  # Wednesday: 13:30 to 16:00 [810,960)
         (16 * 60 + 30, 17 * 60) ],# Wednesday: 16:30 to 17:00 [990,1020)
    3: [ (9 * 60, 9 * 60 + 30),    # Thursday: 9:00 to 9:30 [540,570)
         (10 * 60, 13 * 60 + 30),  # Thursday: 10:00 to 13:30 [600,810)
         (14 * 60, 17 * 60) ],     # Thursday: 14:00 to 17:00 [840,1020)
}

# Utility function to ensure that a meeting starting at 's' (lasting for 'duration')
# does not overlap a busy interval [busy_start, busy_end)
def no_overlap(busy_start, busy_end, s):
    return Or(s + duration <= busy_start, s >= busy_end)

# Candidate days to consider: Monday, Tuesday, Wednesday, Thursday in that order.
candidate_days = [0, 1, 2, 3]

# Function to find an available meeting time on one candidate day.
def find_meeting_time(days):
    for day in days:
        solver = Solver()
        # Define meeting start time variable (in minutes from midnight)
        s = Int("s")
        solver.add(s >= WORK_START, s + duration <= WORK_END)
        
        # Add John's busy intervals for this day.
        for interval in john_busy.get(day, []):
            busy_start, busy_end = interval
            solver.add(no_overlap(busy_start, busy_end, s))
        
        # Try to find the earliest meeting time on this day by trying each minute.
        for t in range(WORK_START, WORK_END - duration + 1):  # meeting must finish by WORK_END
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
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}.".format(
        day_names[selected_day], start_hour, start_minute, end_hour, end_minute))
else:
    print("No valid meeting time could be found that satisfies all constraints.")