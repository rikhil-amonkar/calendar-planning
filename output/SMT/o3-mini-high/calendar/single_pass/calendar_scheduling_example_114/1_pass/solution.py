from z3 import Solver, Int, Or

# Create a solver instance
solver = Solver()

# Define meeting start time in minutes after 9:00.
# The meeting is one hour long so meeting_end = meeting_start + 60.
meeting_start = Int('meeting_start')

# Constraint: Meeting must be within the work day: 9:00 (0 minutes) to 17:00 (480 minutes).
solver.add(meeting_start >= 0)
solver.add(meeting_start + 60 <= 480)

# Busy intervals for each participant (all times in minutes relative to 9:00):
# Stephanie: busy 10:00-10:30  => (60, 90) and 16:00-16:30  => (420, 450)
# Cheryl: busy 10:00-10:30  => (60, 90), 11:30-12:00 => (150, 180),
#         13:30-14:00 => (270, 300) and 16:30-17:00 => (450, 480)
# Bradley: busy 9:30-10:00  => (30, 60), 10:30-11:30 => (90, 150),
#          13:30-14:00 => (270, 300), 14:30-15:00 => (330, 360),
#          15:30-17:00 => (390, 480)
# Steven: busy 9:00-12:00   => (0, 180), 13:00-13:30 => (240, 270),
#         14:30-17:00 => (330, 480)

busy_intervals = [
    # Stephanie
    (60, 90), (420, 450),
    # Cheryl
    (60, 90), (150, 180), (270, 300), (450, 480),
    # Bradley
    (30, 60), (90, 150), (270, 300), (330, 360), (390, 480),
    # Steven
    (0, 180), (240, 270), (330, 480)
]

# For each busy interval, ensure that the meeting does NOT overlap with it.
# The meeting interval is [meeting_start, meeting_start+60).
# It does not overlap with a busy interval [b_start, b_end) if:
#    meeting_start + 60 <= b_start   OR   meeting_start >= b_end
for b_start, b_end in busy_intervals:
    solver.add(Or(meeting_start + 60 <= b_start, meeting_start >= b_end))

# Check if a solution exists.
if solver.check() == 'sat' or solver.check() == True:
    model = solver.model()
    start_val = model[meeting_start].as_long()
    end_val = start_val + 60

    # Helper function: Convert minutes since 9:00 to a clock time (24-hour HH:MM format).
    def minutes_to_time(minutes_after_9):
        # 9:00 is 9*60 = 540 minutes after midnight.
        total_minutes = minutes_after_9 + 9 * 60
        hour = total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"

    start_time_str = minutes_to_time(start_val)
    end_time_str = minutes_to_time(end_val)

    # Output must follow the exact format.
    print("SOLUTION:")
    print("Day: Monday")
    print("Start Time: " + start_time_str)
    print("End Time: " + end_time_str)
else:
    print("No solution found")