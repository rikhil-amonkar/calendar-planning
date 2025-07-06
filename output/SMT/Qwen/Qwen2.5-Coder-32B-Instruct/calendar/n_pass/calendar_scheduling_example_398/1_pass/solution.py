from z3 import *

# Define the time slots as integers representing minutes since 9:00 AM
start_time = 9 * 60  # 9:00 AM
end_time = 17 * 60   # 5:00 PM
meeting_duration = 30  # 30 minutes

# Define the variables for the meeting start time
meeting_start = Int('meeting_start')

# Define the constraints for each person
constraints = [
    # Doris: 9:00 to 11:00, 13:30 to 14:00, 16:00 to 16:30
    Or(meeting_start + meeting_duration <= 11 * 60, meeting_start >= 13 * 60 + 30),
    Or(meeting_start + meeting_duration <= 13 * 60 + 30, meeting_start >= 14 * 60),
    Or(meeting_start + meeting_duration <= 16 * 60, meeting_start >= 16 * 60 + 30),

    # Theresa: 10:00 to 12:00
    Or(meeting_start + meeting_duration <= 10 * 60, meeting_start >= 12 * 60),

    # Christian: No meetings the whole day
    # No additional constraints needed

    # Terry: 9:30 to 10:00, 11:30 to 12:00, 12:30 to 13:00, 13:30 to 14:00, 14:30 to 15:00, 15:30 to 17:00
    Or(meeting_start + meeting_duration <= 9 * 60 + 30, meeting_start >= 10 * 60),
    Or(meeting_start + meeting_duration <= 11 * 60 + 30, meeting_start >= 12 * 60),
    Or(meeting_start + meeting_duration <= 12 * 60 + 30, meeting_start >= 13 * 60),
    Or(meeting_start + meeting_duration <= 13 * 60 + 30, meeting_start >= 14 * 60),
    Or(meeting_start + meeting_duration <= 14 * 60 + 30, meeting_start >= 15 * 60),
    Or(meeting_start + meeting_duration <= 15 * 60 + 30, meeting_start >= 17 * 60),

    # Carolyn: 9:00 to 10:30, 11:00 to 11:30, 12:00 to 13:00, 13:30 to 14:30, 15:00 to 17:00
    Or(meeting_start + meeting_duration <= 10 * 60 + 30, meeting_start >= 11 * 60),
    Or(meeting_start + meeting_duration <= 11 * 60, meeting_start >= 11 * 60 + 30),
    Or(meeting_start + meeting_duration <= 12 * 60, meeting_start >= 13 * 60),
    Or(meeting_start + meeting_duration <= 13 * 60 + 30, meeting_start >= 14 * 60 + 30),
    Or(meeting_start + meeting_duration <= 15 * 60, meeting_start >= 17 * 60),

    # Kyle: 9:00 to 9:30, 11:30 to 12:00, 12:30 to 13:00, 14:30 to 17:00
    Or(meeting_start + meeting_duration <= 9 * 60 + 30, meeting_start >= 11 * 60 + 30),
    Or(meeting_start + meeting_duration <= 11 * 60 + 30, meeting_start >= 12 * 60),
    Or(meeting_start + meeting_duration <= 12 * 60 + 30, meeting_start >= 13 * 60),
    Or(meeting_start + meeting_duration <= 14 * 60 + 30, meeting_start >= 17 * 60),

    # Meeting must start within work hours
    And(meeting_start >= start_time, meeting_start + meeting_duration <= end_time)
]

# Create the solver and add the constraints
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_start_minutes = model[meeting_start].as_long()
    meeting_start_time = f"{(meeting_start_minutes // 60):02}:{(meeting_start_minutes % 60):02}"
    meeting_end_time = f"{((meeting_start_minutes + meeting_duration) // 60):02}:{((meeting_start_minutes + meeting_duration) % 60):02}"
    print(f"SOLUTION:\nDay: Monday\nStart Time: {meeting_start_time}\nEnd Time: {meeting_end_time}")
else:
    print("No solution found")