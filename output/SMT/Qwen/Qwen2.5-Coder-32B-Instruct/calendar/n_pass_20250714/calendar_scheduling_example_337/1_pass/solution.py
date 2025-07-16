from z3 import *

# Define the time intervals in minutes from 9:00 to 17:00
start_time = 9 * 60
end_time = 17 * 60
meeting_duration = 30

# Define the participants and their busy intervals
participants = {
    "John": [(11*60 + 30, 12*60), (14*60, 14*60 + 30)],
    "Megan": [(12*60, 12*60 + 30), (14*60, 15*60), (15*60 + 30, 16*60)],
    "Brandon": [],
    "Kimberly": [(9*60, 9*60 + 30), (10*60, 10*60 + 30), (11*60, 14*60 + 30), (15*60, 16*60), (16*60 + 30, 17*60)],
    "Sean": [(10*60, 11*60), (11*60 + 30, 14*60), (15*60, 15*60 + 30)],
    "Lori": [(9*60, 9*60 + 30), (10*60 + 30, 12*60), (13*60, 14*60 + 30), (16*60, 16*60 + 30)]
}

# Create a solver instance
solver = Solver()

# Define the start time of the meeting as a variable
meeting_start = Int('meeting_start')

# Add constraints for the meeting to fit within the working hours and duration
solver.add(meeting_start >= start_time)
solver.add(meeting_start + meeting_duration <= end_time)

# Add constraints for each participant's availability
for participant, busy_intervals in participants.items():
    # The meeting should not overlap with any busy interval
    for start, end in busy_intervals:
        solver.add(Or(meeting_start + meeting_duration <= start, meeting_start >= end))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_start_value = model[meeting_start].as_long()
    meeting_end_value = meeting_start_value + meeting_duration
    
    # Convert the times back to HH:MM format
    start_hour = meeting_start_value // 60
    start_minute = meeting_start_value % 60
    end_hour = meeting_end_value // 60
    end_minute = meeting_end_value % 60
    
    print(f"SOLUTION:\nDay: Monday\nStart Time: {start_hour:02}:{start_minute:02}\nEnd Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found")