from z3 import *

# Define meeting variables: start time in minutes from midnight
start = Int('start')
duration = 30
end = start + duration

# Define work hours (9:00 to 17:00) in minutes from midnight
work_start = 9 * 60    # 540
work_end   = 17 * 60   # 1020

# Frank's constraint: he does not want to meet after 9:30.
# Interpretation: the meeting must end by 9:30 (i.e., before any time after 9:30)
frank_cutoff = 9 * 60 + 30  # 570

# Create solver instance
s = Solver()

# Meeting must be within the work hours.
s.add(start >= work_start)
s.add(end <= work_end)

# Frank's preference: the meeting must end by 9:30.
s.add(end <= frank_cutoff)

# A helper function that adds a non-overlap constraint for a busy interval.
def add_no_overlap(solver, busy_start, busy_end):
    # The meeting (start, end) must either finish before busy_start or start after busy_end.
    solver.add(Or(end <= busy_start, start >= busy_end))

# Define busy intervals (in minutes from midnight) for each participant.

# Emily's busy intervals on Monday:
# 10:00-10:30, 11:30-12:30, 14:00-15:00, and 16:00-16:30.
emily_busy = [
    (10 * 60, 10 * 60 + 30),     # 600 to 630
    (11 * 60 + 30, 12 * 60 + 30),  # 690 to 750
    (14 * 60, 15 * 60),           # 840 to 900
    (16 * 60, 16 * 60 + 30)       # 960 to 990
]
for busy in emily_busy:
    add_no_overlap(s, busy[0], busy[1])

# Melissa's busy intervals on Monday:
# 9:30-10:00 and 14:30-15:00.
melissa_busy = [
    (9 * 60 + 30, 10 * 60),       # 570 to 600
    (14 * 60 + 30, 15 * 60)       # 870 to 900
]
for busy in melissa_busy:
    add_no_overlap(s, busy[0], busy[1])

# Frank's busy intervals on Monday:
# 10:00-10:30, 11:00-11:30, 12:30-13:00, 13:30-14:30, 15:00-16:00, and 16:30-17:00.
frank_busy = [
    (10 * 60, 10 * 60 + 30),      # 600 to 630
    (11 * 60, 11 * 60 + 30),      # 660 to 690
    (12 * 60 + 30, 13 * 60),      # 750 to 780
    (13 * 60 + 30, 14 * 60 + 30), # 810 to 870
    (15 * 60, 16 * 60),          # 900 to 960
    (16 * 60 + 30, 17 * 60)       # 990 to 1020
]
for busy in frank_busy:
    add_no_overlap(s, busy[0], busy[1])

# Check the constraints and print the solution.
if s.check() == sat:
    m = s.model()
    meeting_start = m[start].as_long()
    meeting_end = meeting_start + duration

    # Convert minutes to HH:MM format.
    start_hour = meeting_start // 60
    start_minute = meeting_start % 60
    end_hour = meeting_end // 60
    end_minute = meeting_end % 60

    # Print the day and time range.
    print("Monday")
    print("{:02d}:{:02d}:{:02d}:{:02d}".format(start_hour, start_minute, end_hour, end_minute))
else:
    print("No solution found.")