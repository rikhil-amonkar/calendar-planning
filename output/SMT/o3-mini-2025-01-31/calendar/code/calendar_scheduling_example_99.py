from z3 import *

# Create a Z3 solver instance
solver = Solver()

# Define meeting_start as an integer (minutes after 9:00)
meeting_start = Int('meeting_start')
meeting_duration = 60  # 60 minutes
# meeting_end = meeting_start + meeting_duration, defined later as needed

# Working hours: 9:00 to 17:00 (i.e., meeting_start + 60 <= 480 minutes since 9:00)
solver.add(meeting_start >= 0, meeting_start + meeting_duration <= 480)

# Mark's preference: avoid meetings before 15:00 (15:00 is 360 minutes after 9:00)
solver.add(meeting_start >= 360)

# Helper function to ensure no overlap between meeting and a busy interval
def no_overlap(meeting_start, meeting_duration, busy_start, busy_end):
    meeting_end = meeting_start + meeting_duration
    return Or(meeting_end <= busy_start, meeting_start >= busy_end)

# Add constraints for Stephanie's busy times:
# Busy from 9:00 to 9:30  --> [0, 30]
# Busy from 13:30 to 14:00 --> [270, 300]
solver.add(no_overlap(meeting_start, meeting_duration, 0, 30))
solver.add(no_overlap(meeting_start, meeting_duration, 270, 300))

# Add constraints for Scott's busy times:
# Busy from 9:00 to 10:00   --> [0, 60]
# Busy from 11:00 to 12:30  --> [120, 210]
# Busy from 14:30 to 15:00  --> [330, 360]
# Busy from 16:00 to 17:00  --> [420, 480]
solver.add(no_overlap(meeting_start, meeting_duration, 0, 60))
solver.add(no_overlap(meeting_start, meeting_duration, 120, 210))
solver.add(no_overlap(meeting_start, meeting_duration, 330, 360))
solver.add(no_overlap(meeting_start, meeting_duration, 420, 480))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    start_val = model[meeting_start].as_long()  # minutes from 9:00

    # Compute meeting start time and end time in HH:MM format.
    start_hour = 9 + start_val // 60
    start_min = start_val % 60
    end_val = start_val + meeting_duration
    end_hour = 9 + end_val // 60
    end_min = end_val % 60

    print("Meeting scheduled from %02d:%02d to %02d:%02d" % (start_hour, start_min, end_hour, end_min))
else:
    print("No valid meeting time could be found.")