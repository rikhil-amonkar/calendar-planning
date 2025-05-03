from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30  # meeting duration in minutes
WORK_START = 9 * 60    # 9:00 in minutes (540)
WORK_END   = 17 * 60   # 17:00 in minutes (1020)

# Days encoded as: Monday=0, Tuesday=1, Wednesday=2, Thursday=3.
# Megan would like to avoid additional meetings on Monday, Tuesday, Wednesday.
# So we prioritize scheduling on Thursday, but if no suitable time is available, we will try the other days.
candidate_days = [3, 0, 1, 2]

# Megan's busy schedule (times in minutes from midnight)
# If a day is not mentioned, assume Megan is free for that day.
megan_busy = {
    0: [ (10 * 60, 10 * 60 + 30),   # Monday: 10:00 to 10:30 -> [600,630)
         (13 * 60, 14 * 60),        # Monday: 13:00 to 14:00 -> [780,840)
         (14 * 60 + 30, 15 * 60) ],  # Monday: 14:30 to 15:00 -> [870,900)
    1: [ (10 * 60 + 30, 11 * 60) ],  # Tuesday: 10:30 to 11:00 -> [630,660)
    2: [ (16 * 60, 16 * 60 + 30) ],  # Wednesday: 16:00 to 16:30 -> [960,990)
    # Thursday: Megan has no busy intervals.
}

# Beverly's busy schedule
beverly_busy = {
    0: [ (9 * 60, 10 * 60 + 30),    # Monday: 9:00 to 10:30 -> [540,630)
         (11 * 60, 11 * 60 + 30),   # Monday: 11:00 to 11:30 -> [660,690)
         (12 * 60 + 30, 13 * 60 + 30), # Monday: 12:30 to 13:30 -> [750,810)
         (14 * 60 + 30, 16 * 60 + 30) ], # Monday: 14:30 to 16:30 -> [870,990)
    1: [ (9 * 60, 10 * 60),        # Tuesday: 9:00 to 10:00 -> [540,600)
         (10 * 60 + 30, 17 * 60) ], # Tuesday: 10:30 to 17:00 -> [630,1020)
    2: [ (9 * 60, 10 * 60 + 30),    # Wednesday: 9:00 to 10:30 -> [540,630)
         (12 * 60, 13 * 60),        # Wednesday: 12:00 to 13:00 -> [720,780)
         (14 * 60, 14 * 60 + 30),    # Wednesday: 14:00 to 14:30 -> [840,870)
         (16 * 60, 17 * 60) ],       # Wednesday: 16:00 to 17:00 -> [960,1020)
    3: [ (10 * 60 + 30, 11 * 60 + 30),  # Thursday: 10:30 to 11:30 -> [630,690)
         (12 * 60 + 30, 13 * 60),        # Thursday: 12:30 to 13:00 -> [750,780)
         (14 * 60, 14 * 60 + 30),        # Thursday: 14:00 to 14:30 -> [840,870)
         (15 * 60 + 30, 17 * 60) ],       # Thursday: 15:30 to 17:00 -> [930,1020)
}

# Helper function: ensures that a meeting starting at s (lasting 'duration' minutes)
# does not overlap a busy interval [busy_start, busy_end).
def no_overlap(busy_start, busy_end, s):
    return Or(s + duration <= busy_start, s >= busy_end)

# Function to find an available meeting time given a list of candidate days.
def find_meeting_time(days):
    # Iterate over candidate days in the order of preference.
    for day in days:
        solver = Solver()
        s = Int("s")  # meeting start time in minutes from midnight

        # Meeting must be within work hours
        solver.add(s >= WORK_START, s + duration <= WORK_END)
        
        # Additional constraint for Beverly on Thursday:
        # Beverly would rather not meet on Thursday after 14:30.
        # So, if day is Thursday (3), the meeting must finish by 14:30.
        if day == 3:
            solver.add(s + duration <= 14 * 60 + 30)  # 14:30 is 870 minutes

        # Add Megan's busy constraints for the day (if any)
        for interval in megan_busy.get(day, []):
            busy_start, busy_end = interval
            solver.add(no_overlap(busy_start, busy_end, s))

        # Add Beverly's busy constraints for the day
        for interval in beverly_busy.get(day, []):
            busy_start, busy_end = interval
            solver.add(no_overlap(busy_start, busy_end, s))

        # Determine the search start time.
        # For Thursday, our constraints already restrict the end; we still start from WORK_START.
        search_start = WORK_START
        search_end = WORK_END - duration + 1
        if day == 3:
            # if meeting must finish by 14:30, then the latest start time is 14:00.
            search_end = min(search_end, 14 * 60 + 1)

        # Search minute-by-minute for a feasible start time.
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