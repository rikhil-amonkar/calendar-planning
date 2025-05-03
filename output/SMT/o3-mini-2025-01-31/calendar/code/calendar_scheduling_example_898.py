from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30           # meeting duration in minutes (half an hour)
WORK_START = 9 * 60     # 9:00 = 540 minutes
WORK_END = 17 * 60      # 17:00 = 1020 minutes

# Days encoding:
# 0: Monday, 1: Tuesday, 2: Wednesday, 3: Thursday.
# William does not want to meet on Thursday, so his allowed days are: Monday, Tuesday, Wednesday.
# Carol would rather not meet on Monday or Wednesday, so her allowed days are: Tuesday, Thursday.
# The intersection is Tuesday (day = 1).
candidate_days = [1]

# William's busy intervals (in minutes after midnight):
# Monday: 12:00 to 12:30, 14:30 to 15:00
# Tuesday: 9:00 to 9:30, 16:30 to 17:00
# Wednesday: 9:00 to 9:30, 12:00 to 12:30, 13:00 to 13:30, 16:00 to 16:30
# Thursday: 9:00 to 9:30, 10:30 to 11:00
william_busy = {
    0: [(12 * 60, 12 * 60 + 30), (14 * 60 + 30, 15 * 60)],
    1: [(9 * 60, 9 * 60 + 30), (16 * 60 + 30, 17 * 60)],
    2: [(9 * 60, 9 * 60 + 30), (12 * 60, 12 * 60 + 30),
        (13 * 60, 13 * 60 + 30), (16 * 60, 16 * 60 + 30)],
    3: [(9 * 60, 9 * 60 + 30), (10 * 60 + 30, 11 * 60)]
}

# Carol's busy intervals (in minutes after midnight):
# Monday: 9:00 to 11:30, 12:00 to 13:00, 13:30 to 15:30, 16:00 to 17:00
# Tuesday: 9:30 to 10:00, 10:30 to 17:00
# Wednesday: 9:00 to 10:30, 11:00 to 11:30, 12:00 to 13:30, 14:00 to 16:00, 16:30 to 17:00
# Thursday: 9:30 to 10:00, 10:30 to 11:30, 13:30 to 16:30
carol_busy = {
    0: [(9 * 60, 11 * 60 + 30), (12 * 60, 13 * 60), (13 * 60 + 30, 15 * 60 + 30), (16 * 60, 17 * 60)],
    1: [(9 * 60 + 30, 10 * 60), (10 * 60 + 30, 17 * 60)],
    2: [(9 * 60, 10 * 60 + 30), (11 * 60, 11 * 60 + 30),
        (12 * 60, 13 * 60 + 30), (14 * 60, 16 * 60), (16 * 60 + 30, 17 * 60)],
    3: [(9 * 60 + 30, 10 * 60), (10 * 60 + 30, 11 * 60 + 30), (13 * 60 + 30, 16 * 60 + 30)]
}

# Utility function: returns a Z3 constraint ensuring that the meeting starting at 's'
# with length 'duration' does NOT overlap with an interval (busy_start, busy_end)
def no_overlap(busy_start, busy_end, s, duration):
    return Or(s + duration <= busy_start, s >= busy_end)

# Function to find a valid meeting time among the candidate days.
def find_meeting_time(days):
    for day in days:
        solver = Solver()
        # 's' is the meeting start time (in minutes after midnight)
        s = Int("s")
        # The meeting must be scheduled within the working hours.
        solver.add(s >= WORK_START, s + duration <= WORK_END)
        
        # Add William's busy intervals for the day.
        if day in william_busy:
            for busy_start, busy_end in william_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))
                
        # Add Carol's busy intervals for the day.
        if day in carol_busy:
            for busy_start, busy_end in carol_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))
                
        # Iterate over each potential start time from WORK_START to last possible start time.
        for t in range(WORK_START, WORK_END - duration + 1):
            solver.push()
            solver.add(s == t)
            if solver.check() == sat:
                return day, t
            solver.pop()
    return None, None

day, t = find_meeting_time(candidate_days)

if day is not None:
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
    selected_day = day_names[day]
    selected_end = t + duration
    start_hr, start_min = divmod(t, 60)
    end_hr, end_min = divmod(selected_end, 60)
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(selected_day, start_hr, start_min, end_hr, end_min))
else:
    print("No valid meeting time could be found that satisfies all constraints.")