from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30           # the meeting lasts 30 minutes
WORK_START = 9 * 60     # 9:00 in minutes: 540
WORK_END = 17 * 60      # 17:00 in minutes: 1020

# Days encoding:
# 0: Monday, 1: Tuesday, 2: Wednesday, 3: Thursday
# Preferences:
# • Christian would like to avoid more meetings on Thursday, so he prefers Monday, Tuesday or Wednesday.
# • Abigail does not want to meet on Monday after 9:30, and prefers Tuesday.
# Based on these, we choose Tuesday (day = 1) as the candidate day.
candidate_days = [1]

# Christian's busy intervals (in minutes after midnight):
# Monday: 11:30-12:00, 13:30-14:00, 15:00-15:30
# Tuesday: 10:00-10:30, 14:00-14:30
# Wednesday: 10:00-11:00, 12:00-12:30, 13:00-14:30, 15:00-15:30, 16:00-17:00
# Thursday: 10:30-11:00, 13:00-13:30
christian_busy = {
    0: [(11 * 60 + 30, 12 * 60), (13 * 60 + 30, 14 * 60), (15 * 60, 15 * 60 + 30)],
    1: [(10 * 60, 10 * 60 + 30), (14 * 60, 14 * 60 + 30)],
    2: [(10 * 60, 11 * 60), (12 * 60, 12 * 60 + 30), (13 * 60, 14 * 60 + 30), (15 * 60, 15 * 60 + 30), (16 * 60, 17 * 60)],
    3: [(10 * 60 + 30, 11 * 60), (13 * 60, 13 * 60 + 30)]
}

# Abigail's busy intervals (in minutes after midnight):
# Monday: 9:30-10:00, 10:30-12:30, 13:00-14:30, 15:00-17:00
# Tuesday: 9:00-9:30, 10:00-12:00, 12:30-13:30, 14:00-16:30
# Wednesday: 9:00-10:30, 11:00-14:00, 14:30-17:00
# Thursday: 9:00-10:30, 11:30-12:30, 14:30-15:00, 15:30-16:00, 16:30-17:00
abigail_busy = {
    0: [(9 * 60 + 30, 10 * 60), (10 * 60 + 30, 12 * 60 + 30), (13 * 60, 14 * 60 + 30), (15 * 60, 17 * 60)],
    1: [(9 * 60, 9 * 60 + 30), (10 * 60, 12 * 60), (12 * 60 + 30, 13 * 60 + 30), (14 * 60, 16 * 60 + 30)],
    2: [(9 * 60, 10 * 60 + 30), (11 * 60, 14 * 60), (14 * 60 + 30, 17 * 60)],
    3: [(9 * 60, 10 * 60 + 30), (11 * 60 + 30, 12 * 60 + 30), (14 * 60 + 30, 15 * 60), (15 * 60 + 30, 16 * 60), (16 * 60 + 30, 17 * 60)]
}

# Utility function to assert that a meeting starting at s with length 'duration'
# does not overlap a busy interval (busy_start, busy_end).
def no_overlap(busy_start, busy_end, s, duration):
    return Or(s + duration <= busy_start, s >= busy_end)

# Find an available meeting time on one of the candidate days.
def find_meeting_time(days):
    for day in days:
        solver = Solver()
        # s: meeting start time (in minutes after midnight)
        s = Int("s")
        # The meeting must occur within working hours.
        solver.add(s >= WORK_START, s + duration <= WORK_END)
        
        # Add Christian's busy constraints for the day.
        if day in christian_busy:
            for busy_start, busy_end in christian_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))
        
        # Add Abigail's busy constraints for the day.
        if day in abigail_busy:
            for busy_start, busy_end in abigail_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))
                
        # Try each possible start time within the working hours.
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
    meeting_end = t + duration
    start_hr, start_min = divmod(t, 60)
    end_hr, end_min = divmod(meeting_end, 60)
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(selected_day, start_hr, start_min, end_hr, end_min))
else:
    print("No valid meeting time could be found that satisfies all constraints.")