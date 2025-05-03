from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30  # meeting duration in minutes
WORK_START = 9 * 60    # 9:00 in minutes (540)
WORK_END   = 17 * 60   # 17:00 in minutes (1020)

# Encode days as: Monday = 0, Tuesday = 1, Wednesday = 2, Thursday = 3.
# Doris cannot meet on Monday, Tuesday. Jeremy would rather not meet on Thursday.
# So we try candidate days in order: Wednesday (2) first, then Thursday (3).
candidate_days = [2, 3]

# Doris' busy schedule: times in minutes from midnight
doris_busy = {
    0: [ (11 * 60 + 30, 12 * 60) ],        # Monday: 11:30 to 12:00
    2: [ (9 * 60, 9 * 60 + 30),             # Wednesday: 9:00 to 9:30
         (11 * 60, 11 * 60 + 30) ],         # Wednesday: 11:00 to 11:30
    3: [ (10 * 60 + 30, 11 * 60) ],          # Thursday: 10:30 to 11:00
}

# Jeremy's busy schedule
jeremy_busy = {
    0: [ (9 * 60, 9 * 60 + 30),             # Monday: 9:00 to 9:30
         (12 * 60 + 30, 13 * 60 + 30),       # Monday: 12:30 to 13:30
         (14 * 60 + 30, 15 * 60),            # Monday: 14:30 to 15:00
         (15 * 60 + 30, 16 * 60 + 30) ],      # Monday: 15:30 to 16:30
    1: [ (9 * 60, 9 * 60 + 30),             # Tuesday: 9:00 to 9:30
         (10 * 60 + 30, 11 * 60),            # Tuesday: 10:30 to 11:00
         (11 * 60 + 30, 12 * 60),            # Tuesday: 11:30 to 12:00
         (12 * 60 + 30, 14 * 60),            # Tuesday: 12:30 to 14:00
         (14 * 60 + 30, 15 * 60 + 30),        # Tuesday: 14:30 to 15:30
         (16 * 60, 17 * 60)],                # Tuesday: 16:00 to 17:00
    2: [ (9 * 60, 10 * 60 + 30),            # Wednesday: 9:00 to 10:30
         (11 * 60, 17 * 60) ],              # Wednesday: 11:00 to 17:00
    3: [ (9 * 60, 12 * 60 + 30),             # Thursday: 9:00 to 12:30
         (13 * 60, 15 * 60),                # Thursday: 13:00 to 15:00
         (15 * 60 + 30, 16 * 60 + 30) ],     # Thursday: 15:30 to 16:30
}

# Helper function: meeting starting at 's' (lasting 'duration') must not overlap a busy interval [busy_start, busy_end)
def no_overlap(busy_start, busy_end, s):
    return Or(s + duration <= busy_start, s >= busy_end)

# Function to find an available meeting time given candidate days.
def find_meeting_time(days):
    for day in days:
        solver = Solver()
        s = Int("s")  # meeting start time in minutes from midnight
        
        # Meeting must occur within work hours.
        solver.add(s >= WORK_START, s + duration <= WORK_END)
        
        # Add Doris' busy intervals for the day.
        for interval in doris_busy.get(day, []):
            busy_start, busy_end = interval
            solver.add(no_overlap(busy_start, busy_end, s))
        
        # Add Jeremy's busy intervals for the day.
        for interval in jeremy_busy.get(day, []):
            busy_start, busy_end = interval
            solver.add(no_overlap(busy_start, busy_end, s))
        
        # Define the range for search.
        search_start = WORK_START
        search_end = WORK_END - duration + 1
        
        # Attempt minute-by-minute search for a valid meeting start time.
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
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(day_names[selected_day], start_hour, start_minute, end_hour, end_minute))
else:
    print("No valid meeting time could be found that satisfies all constraints.")