from z3 import *

# Define the days of the week as integers
MONDAY, TUESDAY, WEDNESDAY, THURSDAY, FRIDAY = 0, 1, 2, 3, 4

# Define the meeting duration
meeting_duration = 60  # in minutes

# Define the time slots in minutes from 9:00 to 17:00
start_time = 9 * 60  # 9:00 in minutes
end_time = 17 * 60   # 17:00 in minutes

# Create a solver instance
solver = Solver()

# Define variables for the meeting day and start time
meeting_day = Int('meeting_day')
meeting_start = Int('meeting_start')

# Add constraints for the meeting day
solver.add(meeting_day >= MONDAY)
solver.add(meeting_day <= FRIDAY)

# Add constraints for the meeting start time
solver.add(meeting_start >= start_time)
solver.add(meeting_start + meeting_duration <= end_time)

# Define the unavailability periods for Nicole and Daniel
nicole_unavailable = [
    (TUESDAY, 16 * 60, 16 * 60 + 30),
    (WEDNESDAY, 15 * 60, 15 * 60 + 30),
    (FRIDAY, 12 * 60, 12 * 60 + 30),
    (FRIDAY, 15 * 60 + 30, 16 * 60)
]

daniel_unavailable = [
    (MONDAY, 9 * 60, 12 * 60 + 30),
    (MONDAY, 13 * 60, 13 * 60 + 30),
    (MONDAY, 14 * 60, 16 * 60 + 30),
    (TUESDAY, 9 * 60, 10 * 60 + 30),
    (TUESDAY, 11 * 60 + 30, 12 * 60 + 30),
    (TUESDAY, 13 * 60, 13 * 60 + 30),
    (TUESDAY, 15 * 60, 16 * 60),
    (TUESDAY, 16 * 60 + 30, 17 * 60),
    (WEDNESDAY, 9 * 60, 10 * 60),
    (WEDNESDAY, 11 * 60, 12 * 60 + 30),
    (WEDNESDAY, 13 * 60, 13 * 60 + 30),
    (WEDNESDAY, 14 * 60, 14 * 60 + 30),
    (WEDNESDAY, 16 * 60 + 30, 17 * 60),
    (THURSDAY, 11 * 60, 12 * 60),
    (THURSDAY, 13 * 60, 14 * 60),
    (THURSDAY, 15 * 60, 15 * 60 + 30),
    (FRIDAY, 10 * 60, 11 * 60),
    (FRIDAY, 11 * 60 + 30, 12 * 60),
    (FRIDAY, 12 * 60 + 30, 14 * 60 + 30),
    (FRIDAY, 15 * 60, 15 * 60 + 30),
    (FRIDAY, 16 * 60, 16 * 60 + 30)
]

# Add constraints to avoid Nicole's unavailable periods
for day, start, end in nicole_unavailable:
    solver.add(Or(meeting_day != day, Or(meeting_start + meeting_duration <= start, meeting_start >= end)))

# Add constraints to avoid Daniel's unavailable periods
for day, start, end in daniel_unavailable:
    solver.add(Or(meeting_day != day, Or(meeting_start + meeting_duration <= start, meeting_start >= end)))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_day_value = model[meeting_day].as_long()
    meeting_start_value = model[meeting_start].as_long()
    
    # Convert the day and start time to human-readable format
    days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    meeting_day_str = days[meeting_day_value]
    meeting_start_str = f"{meeting_start_value // 60:02}:{meeting_start_value % 60:02}"
    meeting_end_str = f"{(meeting_start_value + meeting_duration) // 60:02}:{(meeting_start_value + meeting_duration) % 60:02}"
    
    print(f"SOLUTION:\nDay: {meeting_day_str}\nStart Time: {meeting_start_str}\nEnd Time: {meeting_end_str}")
else:
    print("No solution found")