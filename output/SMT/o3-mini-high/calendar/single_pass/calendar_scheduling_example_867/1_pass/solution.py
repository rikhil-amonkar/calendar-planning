from z3 import *

# Mapping of days to integer values.
# Monday = 0, Tuesday = 1, Wednesday = 2, Thursday = 3.
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}

# Meeting duration in minutes
duration = 30

# Working hours: meeting must be between 09:00 (540 minutes) and 17:00 (1020 minutes).
work_start = 540
work_end = 1020  # meeting must end by this time

# Create Z3 solver
solver = Solver()

# Decision variables:
# day: an integer in {0,1,2,3} representing the meeting day
day = Int('day')
# start: the start time (in minutes from midnight) for the meeting.
start = Int('start')
end = start + duration  # meeting end time

# Domain constraints
solver.add(Or(day == 0, day == 1, day == 2, day == 3))
solver.add(start >= work_start, end <= work_end)

# Additional participant-specific constraints:
# Betty does not want to meet on Monday.
solver.add(day != 0)
# Betty cannot meet on Tuesday or Thursday before 15:00 (15:00 = 900 minutes).
solver.add(Implies(day == 1, start >= 900))
solver.add(Implies(day == 3, start >= 900))
# Scott would like to avoid more meetings on Wednesday.
# We model this as a hard constraint (since other days are possible).
solver.add(day != 2)

# Helper: for each busy interval, if meeting is scheduled on that day, 
# then the meeting time must not overlap with the busy interval.
def add_no_overlap(solver, meeting_day, meeting_start, busy_day, busy_start, busy_end):
    # If meeting is on the busy_day then either meeting ends on or before busy_start
    # or meeting starts on or after busy_end.
    solver.add(Implies(meeting_day == busy_day,
                       Or(meeting_start + duration <= busy_start, meeting_start >= busy_end)))

# Busy intervals for Betty
# Format: (day, busy_start, busy_end) with times in minutes.
betty_busy = [
    # Monday (day 0)
    (0, 10*60, 10*60+30),      # 10:00 - 10:30
    (0, 13*60+30, 14*60),       # 13:30 - 14:00
    (0, 15*60, 15*60+30),       # 15:00 - 15:30
    (0, 16*60, 16*60+30),       # 16:00 - 16:30
    # Tuesday (day 1)
    (1, 9*60, 9*60+30),         # 9:00 - 9:30
    (1, 11*60+30, 12*60),       # 11:30 - 12:00
    (1, 12*60+30, 13*60),       # 12:30 - 13:00
    (1, 13*60+30, 14*60),       # 13:30 - 14:00
    (1, 16*60+30, 17*60),       # 16:30 - 17:00
    # Wednesday (day 2)
    (2, 9*60+30, 10*60+30),     # 9:30 - 10:30
    (2, 13*60, 13*60+30),       # 13:00 - 13:30
    (2, 14*60, 14*60+30),       # 14:00 - 14:30
    # Thursday (day 3)
    (3, 9*60+30, 10*60),        # 9:30 - 10:00
    (3, 11*60+30, 12*60),       # 11:30 - 12:00
    (3, 14*60, 14*60+30),       # 14:00 - 14:30
    (3, 15*60, 15*60+30),       # 15:00 - 15:30
    (3, 16*60+30, 17*60)        # 16:30 - 17:00
]

# Busy intervals for Scott
scott_busy = [
    # Monday (day 0)
    (0, 9*60+30, 15*60),        # 9:30 - 15:00
    (0, 15*60+30, 16*60),        # 15:30 - 16:00
    (0, 16*60+30, 17*60),        # 16:30 - 17:00
    # Tuesday (day 1)
    (1, 9*60, 9*60+30),         # 9:00 - 9:30
    (1, 10*60, 11*60),          # 10:00 - 11:00
    (1, 11*60+30, 12*60),       # 11:30 - 12:00
    (1, 12*60+30, 13*60+30),    # 12:30 - 13:30
    (1, 14*60, 15*60),          # 14:00 - 15:00
    (1, 16*60, 16*60+30),       # 16:00 - 16:30
    # Wednesday (day 2)
    (2, 9*60+30, 12*60+30),     # 9:30 - 12:30
    (2, 13*60, 13*60+30),       # 13:00 - 13:30
    (2, 14*60, 14*60+30),       # 14:00 - 14:30
    (2, 15*60, 15*60+30),       # 15:00 - 15:30
    (2, 16*60, 16*60+30),       # 16:00 - 16:30
    # Thursday (day 3)
    (3, 9*60, 9*60+30),         # 9:00 - 9:30
    (3, 10*60, 10*60+30),       # 10:00 - 10:30
    (3, 11*60, 12*60),          # 11:00 - 12:00
    (3, 12*60+30, 13*60),       # 12:30 - 13:00
    (3, 15*60, 16*60),          # 15:00 - 16:00
    (3, 16*60+30, 17*60)        # 16:30 - 17:00
]

# Add busy constraints for Betty
for (busy_day, busy_start, busy_end) in betty_busy:
    add_no_overlap(solver, day, start, busy_day, busy_start, busy_end)

# Add busy constraints for Scott
for (busy_day, busy_start, busy_end) in scott_busy:
    add_no_overlap(solver, day, start, busy_day, busy_start, busy_end)

# Try to find a solution satisfying all constraints.
if solver.check() == sat:
    m = solver.model()
    chosen_day = m.evaluate(day).as_long()
    chosen_start = m.evaluate(start).as_long()
    chosen_end = chosen_start + duration

    # Helper to convert minutes to HH:MM string format.
    def minutes_to_str(mnts):
        hr = mnts // 60
        mn = mnts % 60
        return f"{hr:02}:{mn:02}"
    
    print("SOLUTION:")
    print(f"Day: {day_names[chosen_day]}")
    print(f"Start Time: {minutes_to_str(chosen_start)}")
    print(f"End Time: {minutes_to_str(chosen_end)}")
else:
    print("No valid meeting time found.")