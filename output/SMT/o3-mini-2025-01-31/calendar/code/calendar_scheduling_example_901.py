from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 60           # meeting duration is 60 minutes (1 hour)
WORK_START = 9 * 60     # 9:00 in minutes => 540
WORK_END = 17 * 60      # 17:00 in minutes => 1020

# Days encoding:
# 0: Monday, 1: Tuesday, 2: Wednesday, 3: Thursday, 4: Friday
# Sean would rather not meet on Thursday, so we choose candidate days as Monday, Tuesday, Wednesday, and Friday.
candidate_days = [0, 1, 2, 4]

# Sean's busy intervals (each tuple is (start, end) in minutes after midnight):
sean_busy = {
    0: [(9 * 60 + 30, 10 * 60), (11 * 60 + 30, 12 * 60), (14 * 60 + 30, 15 * 60)],           # Monday: 9:30-10:00, 11:30-12:00, 14:30-15:00
    1: [(9 * 60, 10 * 60 + 30), (12 * 60, 12 * 60 + 30), (16 * 60 + 30, 17 * 60)],              # Tuesday: 9:00-10:30, 12:00-12:30, 16:30-17:00
    2: [(9 * 60, 9 * 60 + 30), (11 * 60, 11 * 60 + 30), (12 * 60, 12 * 60 + 30), 
        (13 * 60, 13 * 60 + 30), (16 * 60, 16 * 60 + 30)],                                       # Wednesday: 9:00-9:30, 11:00-11:30, 12:00-12:30, 13:00-13:30, 16:00-16:30
    3: [(10 * 60, 12 * 60 + 30), (15 * 60 + 30, 17 * 60)],                                      # Thursday: 10:00-12:30, 15:30-17:00 (not a candidate)
    4: [(9 * 60, 9 * 60 + 30), (12 * 60, 13 * 60), (13 * 60 + 30, 14 * 60), (15 * 60, 16 * 60 + 30)]  # Friday: 9:00-9:30, 12:00-13:00, 13:30-14:00, 15:00-16:30
}

# Paul's busy intervals (each tuple is (start, end) in minutes after midnight):
paul_busy = {
    0: [(10 * 60, 10 * 60 + 30), (11 * 60, 15 * 60 + 30), (16 * 60, 17 * 60)],   # Monday: 10:00-10:30, 11:00-15:30, 16:00-17:00
    1: [(9 * 60, 12 * 60 + 30), (13 * 60, 14 * 60), (14 * 60 + 30, 16 * 60)],        # Tuesday: 9:00-12:30, 13:00-14:00, 14:30-16:00
    2: [(13 * 60 + 30, 14 * 60), (14 * 60 + 30, 15 * 60), (15 * 60 + 30, 16 * 60)],  # Wednesday: 13:30-14:00, 14:30-15:00, 15:30-16:00
    3: [(9 * 60 + 30, 10 * 60 + 30), (11 * 60 + 30, 12 * 60), (13 * 60 + 30, 14 * 60), (16 * 60 + 30, 17 * 60)],  # Thursday: 9:30-10:30, 11:30-12:00, 13:30-14:00, 16:30-17:00
    4: [(10 * 60, 10 * 60 + 30), (11 * 60, 11 * 60 + 30), (12 * 60, 13 * 60), (14 * 60, 14 * 60 + 30),
        (15 * 60, 16 * 60), (16 * 60 + 30, 17 * 60)]  # Friday: 10:00-10:30, 11:00-11:30, 12:00-13:00, 14:00-14:30, 15:00-16:00, 16:30-17:00
}

# Utility function: returns a Z3 constraint that ensures a meeting starting at 's' with length 'duration'
# does NOT overlap with a busy interval (busy_start, busy_end)
def no_overlap(busy_start, busy_end, s, duration):
    return Or(s + duration <= busy_start, s >= busy_end)

# Function to find an available meeting time on the candidate days,
# trying each day in order and scheduling at the earliest possible time.
def find_meeting_time(days):
    for day in days:
        solver = Solver()
        # 's' represents the meeting start time (minutes after midnight)
        s = Int("s")
        # Meeting must occur entirely within working hours.
        solver.add(s >= WORK_START, s + duration <= WORK_END)
        
        # Add Sean's busy constraints for this day.
        if day in sean_busy:
            for busy_start, busy_end in sean_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))
        
        # Add Paul's busy constraints for this day.
        if day in paul_busy:
            for busy_start, busy_end in paul_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))
        
        # Try every possible start time from WORK_START to latest start time.
        for t in range(WORK_START, WORK_END - duration + 1):
            solver.push()
            solver.add(s == t)
            if solver.check() == sat:
                return day, t
            solver.pop()
    return None, None

day, t = find_meeting_time(candidate_days)

if day is not None:
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}
    selected_day = day_names[day]
    meeting_end = t + duration
    start_hr, start_min = divmod(t, 60)
    end_hr, end_min = divmod(meeting_end, 60)
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(selected_day, start_hr, start_min, end_hr, end_min))
else:
    print("No valid meeting time could be found that satisfies all constraints.")