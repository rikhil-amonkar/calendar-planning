from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30            # meeting duration in minutes
WORK_START = 9 * 60      # 9:00 in minutes (540)
WORK_END   = 17 * 60     # 17:00 in minutes (1020)

# Encode days as: Monday=0, Tuesday=1, Wednesday=2, Thursday=3.
# Constraints:
# - Jacob does not want to meet on Thursday, so his available days are Monday, Tuesday, or Wednesday.
# - Beverly is fully booked on Monday.
# - Beverly would like to avoid Tuesday and also avoid Wednesday meetings that start before 16:00.
# Given that preference, we prioritize scheduling on Wednesday (with meeting starting at or after 16:00)
# over Tuesday. (Tuesday is only used as a fallback option if Wednesday isn’t possible.)
candidate_days = [2, 1]  # 2: Wednesday, 1: Tuesday

# Jacob's busy schedule (times in minutes from midnight):
jacob_busy = {
    0: [ (10 * 60 + 30, 11 * 60),   # Monday: 10:30 - 11:00 [630,660)
         (12 * 60 + 30, 13 * 60),   # Monday: 12:30 - 13:00 [750,780)
         (13 * 60 + 30, 14 * 60 + 30),  # Monday: 13:30 - 14:30 [810,870)
         (16 * 60, 17 * 60) ],      # Monday: 16:00 - 17:00 [960,1020)
    1: [ (9 * 60 + 30, 10 * 60 + 30),   # Tuesday: 9:30 - 10:30 [570,630)
         (12 * 60 + 30, 13 * 60),        # Tuesday: 12:30 - 13:00 [750,780)
         (14 * 60, 14 * 60 + 30),        # Tuesday: 14:00 - 14:30 [840,870)
         (16 * 60, 16 * 60 + 30) ],       # Tuesday: 16:00 - 16:30 [960,990)
    # Jacob has no meetings on Wednesday.
    3: [ (10 * 60, 10 * 60 + 30),   # Thursday: 10:00 - 10:30 [600,630)
         (11 * 60 + 30, 12 * 60 + 30),  # Thursday: 11:30 - 12:30 [690,750)
         (13 * 60, 13 * 60 + 30),      # Thursday: 13:00 - 13:30 [780,810)
         (15 * 60, 16 * 60 + 30) ],     # Thursday: 15:00 - 16:30 [900,990)
}

# Beverly's busy schedule (times in minutes from midnight):
beverly_busy = {
    0: [ (9 * 60, 17 * 60) ],           # Monday: 9:00 - 17:00 [540,1020)
    1: [ (9 * 60, 15 * 60 + 30),         # Tuesday: 9:00 - 15:30 [540,930)
         (16 * 60, 17 * 60) ],           # Tuesday: 16:00 - 17:00 [960,1020)
    2: [ (9 * 60, 12 * 60 + 30),          # Wednesday: 9:00 - 12:30 [540,750)
         (13 * 60 + 30, 14 * 60),         # Wednesday: 13:30 - 14:00 [810,840)
         (14 * 60 + 30, 16 * 60),         # Wednesday: 14:30 - 16:00 [870,960)
         (16 * 60 + 30, 17 * 60) ],       # Wednesday: 16:30 - 17:00 [990,1020)
    3: [ (9 * 60, 11 * 60 + 30),          # Thursday: 9:00 - 11:30 [540,690)
         (12 * 60, 14 * 60),             # Thursday: 12:00 - 14:00 [720,840)
         (15 * 60, 17 * 60) ],           # Thursday: 15:00 - 17:00 [900,1020)
}

# Utility function: meeting starting at 's' for 'duration' minutes must not overlap a busy interval [busy_start, busy_end)
def no_overlap(busy_start, busy_end, s):
    return Or(s + duration <= busy_start, s >= busy_end)

# Function to find an available meeting time on one of the candidate days.
# For each day, we set up the scheduling constraints and search for the earliest possible minute.
def find_meeting_time(days):
    for day in days:
        solver = Solver()
        # Define the meeting start time variable (in minutes from midnight)
        s = Int("s")
        solver.add(s >= WORK_START, s + duration <= WORK_END)
        
        # For each busy interval of Jacob on that day, add non-overlap constraint
        for interval in jacob_busy.get(day, []):
            busy_start, busy_end = interval
            solver.add(no_overlap(busy_start, busy_end, s))
            
        # For each busy interval of Beverly on that day, add non-overlap constraint
        for interval in beverly_busy.get(day, []):
            busy_start, busy_end = interval
            solver.add(no_overlap(busy_start, busy_end, s))
            
        # Add additional preference constraints:
        # Beverly would like to avoid Wednesday meetings that start before 16:00.
        if day == 2:  # Wednesday
            solver.add(s >= 16 * 60)  # force meeting to start at or after 16:00
        
        # Search for the earliest possible meeting time on the day
        search_start = WORK_START
        search_end = WORK_END - duration + 1
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