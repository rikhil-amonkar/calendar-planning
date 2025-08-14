from z3 import *

# Define the variables for the meeting start time in minutes since 9:00 AM
meeting_start = Int('meeting_start')
meeting_duration = 30  # Meeting duration is 30 minutes

# Define the availability of each participant in terms of intervals (in minutes since 9:00 AM)
availability_intervals = {
    'Andrea': [(30, 60), (80, 120)],  # 9:30-10:30, 13:30-14:30
    'Ruth': [(70, 90), (110, 120)],   # 12:30-13:00, 15:00-15:30
    'Steven': [(0, 30), (60, 70), (90, 100), (120, 130), (150, 180)],  # 10:00-10:30, 11:00-11:30, 12:00-12:30, 13:30-14:00, 15:00-16:00
    'Grace': [],  # No meetings the whole day
    'Kyle': [(0, 30), (60, 120), (130, 150), (160, 180), (200, 240)],  # 9:00-9:30, 10:30-12:00, 12:30-13:00, 13:30-15:00, 15:30-16:00, 16:30-17:00
    'Elijah': [(0, 120), (130, 150), (160, 180), (200, 240)],  # 9:00-11:00, 11:30-13:00, 13:30-14:00, 15:30-16:00, 16:30-17:00
    'Lori': [(0, 30), (10, 80), (90, 150), (160, 180), (200, 240)]  # 9:00-9:30, 10:00-11:30, 12:00-13:30, 14:00-16:00, 16:30-17:00
}

# Create a solver instance
solver = Solver()

# Add constraints for the meeting start time
solver.add(meeting_start >= 0)  # Meeting starts at or after 9:00 AM
solver.add(meeting_start + meeting_duration <= 480)  # Meeting ends before or at 17:00 PM

# Add constraints for each participant's availability
for person, intervals in availability_intervals.items():
    # The meeting must not overlap with any of the busy intervals
    for start, end in intervals:
        solver.add(Or(meeting_start + meeting_duration <= start, meeting_start >= end))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    start_time_minutes = model[meeting_start].as_long()
    start_hour = 9 + start_time_minutes // 60
    start_minute = start_time_minutes % 60
    end_hour = start_hour + (start_minute + meeting_duration) // 60
    end_minute = (start_minute + meeting_duration) % 60
    
    print(f"SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {start_hour:02}:{start_minute:02}")
    print(f"End Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found")