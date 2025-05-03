from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30  # meeting duration in minutes
WORK_START = 9 * 60    # 9:00 in minutes (540)
WORK_END   = 17 * 60   # 17:00 in minutes (1020)

# Encode days as: Monday = 0, Tuesday = 1, Wednesday = 2, Thursday = 3.
# Philip does not want to meet on Monday, and Roy prefers that if the meeting is on Wednesday it finishes by 11:00.
# Also note Roy is busy all day on Tuesday.
# Our candidate days in order of preference: try Thursday (3) first, then Wednesday (2). 
candidate_days = [3, 2]

# Philip's busy schedule (times in minutes from midnight)
philip_busy = {
    0: [ (10 * 60, 10 * 60 + 30),   # Monday: 10:00 to 10:30  -> [600,630)
         (11 * 60, 11 * 60 + 30),   # Monday: 11:00 to 11:30  -> [660,690)
         (13 * 60 + 30, 14 * 60 + 30),  # Monday: 13:30 to 14:30 -> [810,870)
         (15 * 60, 17 * 60) ],      # Monday: 15:00 to 17:00  -> [900,1020)
    1: [ (10 * 60 + 30, 11 * 60),   # Tuesday: 10:30 to 11:00 -> [630,660)
         (12 * 60 + 30, 13 * 60 + 30),  # Tuesday: 12:30 to 13:30 -> [750,810)
         (14 * 60, 15 * 60 + 30),    # Tuesday: 14:00 to 15:30 -> [840,930)
         (16 * 60, 16 * 60 + 30) ],  # Tuesday: 16:00 to 16:30 -> [960,990)
    2: [ (9 * 60, 9 * 60 + 30),     # Wednesday: 9:00 to 9:30 -> [540,570)
         (10 * 60, 11 * 60),        # Wednesday: 10:00 to 11:00 -> [600,660)
         (11 * 60 + 30, 12 * 60),   # Wednesday: 11:30 to 12:00 -> [690,720)
         (13 * 60 + 30, 15 * 60) ],  # Wednesday: 13:30 to 15:00 -> [810,900)
    3: [ (9 * 60, 9 * 60 + 30),     # Thursday: 9:00 to 9:30 -> [540,570)
         (11 * 60 + 30, 12 * 60),   # Thursday: 11:30 to 12:00 -> [690,720)
         (14 * 60, 15 * 60),        # Thursday: 14:00 to 15:00 -> [840,900)
         (15 * 60 + 30, 16 * 60),   # Thursday: 15:30 to 16:00 -> [930,960)
         (16 * 60 + 30, 17 * 60) ], # Thursday: 16:30 to 17:00 -> [990,1020)
}

# Roy's busy schedule
roy_busy = {
    0: [ (9 * 60, 10 * 60 + 30),    # Monday: 9:00 to 10:30 -> [540,630)
         (11 * 60, 14 * 60 + 30),   # Monday: 11:00 to 14:30 -> [660,870)
         (15 * 60, 16 * 60 + 30) ],  # Monday: 15:00 to 16:30 -> [900,990)
    1: [ (9 * 60, 17 * 60) ],        # Tuesday: 9:00 to 17:00 -> [540,1020)
    2: [ (10 * 60, 10 * 60 + 30),    # Wednesday: 10:00 to 10:30 -> [600,630)
         (11 * 60, 12 * 60),        # Wednesday: 11:00 to 12:00 -> [660,720)
         (12 * 60 + 30, 14 * 60),   # Wednesday: 12:30 to 14:00 -> [750,840)
         (14 * 60 + 30, 16 * 60),   # Wednesday: 14:30 to 16:00 -> [870,960)
         (16 * 60 + 30, 17 * 60) ],  # Wednesday: 16:30 to 17:00 -> [990,1020)
    3: [ (9 * 60, 12 * 60 + 30),     # Thursday: 9:00 to 12:30 -> [540,750)
         (13 * 60, 17 * 60) ],       # Thursday: 13:00 to 17:00 -> [780,1020)
}

# Helper function: meeting starting at 's' (lasting 'duration' minutes) must not overlap a busy interval [busy_start, busy_end).
def no_overlap(busy_start, busy_end, s):
    return Or(s + duration <= busy_start, s >= busy_end)

# Function to find an available meeting time given candidate days.
def find_meeting_time(days):
    for day in days:
        solver = Solver()
        s = Int("s")  # meeting start time in minutes from midnight

        # Meeting must occur within work hours
        solver.add(s >= WORK_START, s + duration <= WORK_END)

        # Add day-specific preference constraints:
        # Roy wants to avoid meetings on Wednesday after 11:00, so if the meeting is on Wednesday (day 2), it must finish by 11:00.
        if day == 2:
            solver.add(s + duration <= 11 * 60)  # finish by 11:00 (660 minutes)

        # Add Philip's busy intervals for the day, if any.
        for interval in philip_busy.get(day, []):
            busy_start, busy_end = interval
            solver.add(no_overlap(busy_start, busy_end, s))

        # Add Roy's busy intervals for the day.
        for interval in roy_busy.get(day, []):
            busy_start, busy_end = interval
            solver.add(no_overlap(busy_start, busy_end, s))

        # Determine the range for a possible start time.
        search_start = WORK_START
        search_end = WORK_END - duration + 1

        # Further restrict search range if day-specific preference applies.
        if day == 2:
            # Meeting must finish by 11:00 for Wednesday.
            search_end = min(search_end, 11 * 60 - duration + 1)  # Latest start time is 11:00 - duration

        # Attempt minute-by-minute search for a valid start time.
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