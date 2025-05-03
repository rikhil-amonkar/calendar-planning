from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30           # meeting duration in minutes (half an hour)
WORK_START = 9 * 60     # 9:00 in minutes (540)
WORK_END   = 17 * 60    # 17:00 in minutes (1020)

# We encode days as: Monday=0, Tuesday=1, Wednesday=2, Thursday=3.
# Preferences:
#   Ethan would like to avoid more meetings on Thursday.
#   Henry would rather not meet on Tuesday.
# Thus, we choose candidate days as Monday and Wednesday.
candidate_days = [0, 2] 

# Define busy schedules (times are in minutes from midnight).

# Ethan's busy schedule:
ethan_busy = {
    0: [ (10 * 60 + 30, 11 * 60),    # Monday: 10:30 - 11:00 (630, 660)
         (12 * 60, 13 * 60),         # Monday: 12:00 - 13:00 (720, 780)
         (14 * 60 + 30, 15 * 60 + 30) # Monday: 14:30 - 15:30 (870, 930)
       ],
    1: [ (10 * 60 + 30, 11 * 60 + 30), # Tuesday: 10:30 - 11:30 (630, 690)
         (12 * 60 + 30, 13 * 60),      # Tuesday: 12:30 - 13:00 (750, 780)
         (14 * 60, 14 * 60 + 30),      # Tuesday: 14:00 - 14:30 (840, 870)
         (15 * 60 + 30, 16 * 60)       # Tuesday: 15:30 - 16:00 (930, 960)
       ],
    2: [ (9 * 60 + 30, 10 * 60 + 30),  # Wednesday: 9:30 - 10:30 (570, 630)
         (11 * 60 + 30, 12 * 60),      # Wednesday: 11:30 - 12:00 (690, 720)
         (13 * 60, 15 * 60),           # Wednesday: 13:00 - 15:00 (780, 900)
         (16 * 60 + 30, 17 * 60)       # Wednesday: 16:30 - 17:00 (990, 1020)
       ],
    3: [ (11 * 60, 11 * 60 + 30),      # Thursday: 11:00 - 11:30 (660, 690)
         (12 * 60 + 30, 13 * 60),      # Thursday: 12:30 - 13:00 (750, 780)
         (14 * 60, 14 * 60 + 30),      # Thursday: 14:00 - 14:30 (840, 870)
         (15 * 60, 15 * 60 + 30),      # Thursday: 15:00 - 15:30 (900, 930)
         (16 * 60, 17 * 60)           # Thursday: 16:00 - 17:00 (960, 1020)
       ]
}

# Henry's busy schedule:
henry_busy = {
    0: [ (9 * 60 + 30, 10 * 60),      # Monday: 9:30 - 10:00 (570,600)
         (10 * 60 + 30, 13 * 60 + 30),# Monday: 10:30 - 13:30 (630,810)
         (14 * 60, 14 * 60 + 30),     # Monday: 14:00 - 14:30 (840,870)
         (15 * 60 + 30, 17 * 60)      # Monday: 15:30 - 17:00 (930,1020)
       ],
    1: [ (9 * 60, 9 * 60 + 30),       # Tuesday: 9:00 - 9:30 (540,570)
         (10 * 60, 11 * 60),          # Tuesday: 10:00 - 11:00 (600,660)
         (11 * 60 + 30, 14 * 60),     # Tuesday: 11:30 - 14:00 (690,840)
         (14 * 60 + 30, 17 * 60)      # Tuesday: 14:30 - 17:00 (870,1020)
       ],
    2: [ (9 * 60, 9 * 60 + 30),       # Wednesday: 9:00 - 9:30 (540,570)
         (10 * 60, 10 * 60 + 30),     # Wednesday: 10:00 - 10:30 (600,630)
         (11 * 60 + 30, 12 * 60),     # Wednesday: 11:30 - 12:00 (690,720)
         (12 * 60 + 30, 14 * 60),     # Wednesday: 12:30 - 14:00 (750,840)
         (14 * 60 + 30, 16 * 60)      # Wednesday: 14:30 - 16:00 (870,960)
       ],
    3: [ (10 * 60, 11 * 60),          # Thursday: 10:00 - 11:00 (600,660)
         (11 * 60 + 30, 12 * 60),     # Thursday: 11:30 - 12:00 (690,720)
         (13 * 60, 14 * 60),          # Thursday: 13:00 - 14:00 (780,840)
         (15 * 60, 15 * 60 + 30),     # Thursday: 15:00 - 15:30 (900,930)
         (16 * 60, 16 * 60 + 30)      # Thursday: 16:00 - 16:30 (960,990)
       ]
}

# Utility function: For a meeting start time 's' with given duration,
# ensure the meeting does not overlap a busy interval [busy_start, busy_end)
def no_overlap(busy_start, busy_end, s):
    return Or(s + duration <= busy_start, s >= busy_end)

# Function to search for an available meeting time on candidate days.
def find_meeting_time(days):
    for day in days:
        solver = Solver()
        s = Int("s")  # meeting start time in minutes from midnight
        solver.add(s >= WORK_START, s + duration <= WORK_END)
        
        # Add Ethan's busy constraints for the current day.
        for busy_start, busy_end in ethan_busy.get(day, []):
            solver.add(no_overlap(busy_start, busy_end, s))
        
        # Add Henry's busy constraints for the current day.
        for busy_start, busy_end in henry_busy.get(day, []):
            solver.add(no_overlap(busy_start, busy_end, s))
        
        # Try each minute during work hours and return the earliest available slot.
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