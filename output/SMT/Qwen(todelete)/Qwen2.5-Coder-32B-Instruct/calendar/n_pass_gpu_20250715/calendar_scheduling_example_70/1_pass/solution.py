from z3 import *

# Define the time slots in minutes from 9:00 to 17:00
start_of_day = 9 * 60  # 9:00 AM in minutes
end_of_day = 17 * 60   # 5:00 PM in minutes
meeting_duration = 30  # 30 minutes

# Create a variable for the start time of the meeting
meeting_start = Int('meeting_start')

# Define the constraints for each participant
constraints = []

# Denise's constraints: 12:00 to 12:30, 15:30 to 16:00
denise_busy_slots = [(12 * 60, 12 * 60 + 30), (15 * 60 + 30, 16 * 60)]
for start, end in denise_busy_slots:
    constraints.append(Or(meeting_start >= end, meeting_start + meeting_duration <= start))

# Angela has no meetings, so no constraints for her

# Natalie's constraints: 9:00 to 11:30, 12:00 to 13:00, 14:00 to 14:30, 15:00 to 17:00
natalie_busy_slots = [(9 * 60, 11 * 60 + 30), (12 * 60, 13 * 60), (14 * 60, 14 * 60 + 30), (15 * 60, 17 * 60)]
for start, end in natalie_busy_slots:
    constraints.append(Or(meeting_start >= end, meeting_start + meeting_duration <= start))

# Add constraints to ensure the meeting is within working hours
constraints.append(meeting_start >= start_of_day)
constraints.append(meeting_start + meeting_duration <= end_of_day)

# Create a solver instance and add the constraints
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_start_minutes = model[meeting_start].as_long()
    meeting_start_time = f"{meeting_start_minutes // 60:02}:{meeting_start_minutes % 60:02}"
    meeting_end_time = f"{(meeting_start_minutes + meeting_duration) // 60:02}:{(meeting_start_minutes + meeting_duration) % 60:02}"
    print(f"SOLUTION:\nDay: Monday\nStart Time: {meeting_start_time}\nEnd Time: {meeting_end_time}")
else:
    print("No solution found")