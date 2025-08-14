from z3 import *

# Define the time slots in minutes from 9:00 to 17:00 (9 * 60 to 17 * 60)
start_time = 9 * 60
end_time = 17 * 60
meeting_duration = 30

# Create a variable to represent the start time of the meeting in minutes from 9:00
meeting_start = Int('meeting_start')

# Define the constraints for each participant
constraints = [
    # Wayne is free the entire day, so no constraints for him.
    
    # Melissa's constraints
    Or(meeting_start >= 11 * 60, meeting_start + meeting_duration <= 10 * 60),
    Or(meeting_start >= 14 * 60, meeting_start + meeting_duration <= 12 * 30),
    Or(meeting_start >= 15 * 30, meeting_start + meeting_duration <= 15 * 0),
    
    # Catherine is free the entire day, so no constraints for her.
    
    # Gregory's constraints
    Or(meeting_start >= 13 * 0, meeting_start + meeting_duration <= 12 * 30),
    Or(meeting_start >= 16 * 30, meeting_start + meeting_duration <= 15 * 30),
    
    # Victoria's constraints
    Or(meeting_start >= 9 * 30, meeting_start + meeting_duration <= 10 * 30),
    Or(meeting_start >= 11 * 30, meeting_start + meeting_duration <= 13 * 0),
    Or(meeting_start >= 14 * 0, meeting_start + meeting_duration <= 13 * 30),
    Or(meeting_start >= 15 * 0, meeting_start + meeting_duration <= 14 * 30),
    Or(meeting_start >= 16 * 30, meeting_start + meeting_duration <= 15 * 30),
    
    # Thomas's constraints
    Or(meeting_start >= 12 * 0, meeting_start + meeting_duration <= 10 * 60),
    Or(meeting_start >= 13 * 0, meeting_start + meeting_duration <= 12 * 30),
    Or(meeting_start >= 16 * 30, meeting_start + meeting_duration <= 14 * 30),
    
    # Jennifer's constraints
    Or(meeting_start >= 9 * 30, meeting_start + meeting_duration <= 10 * 0),
    Or(meeting_start >= 10 * 30, meeting_start + meeting_duration <= 11 * 0),
    Or(meeting_start >= 13 * 0, meeting_start + meeting_duration <= 11 * 30),
    Or(meeting_start >= 14 * 30, meeting_start + meeting_duration <= 13 * 30),
    Or(meeting_start >= 15 * 30, meeting_start + meeting_duration <= 15 * 0),
    Or(meeting_start >= 16 * 30, meeting_start + meeting_duration <= 16 * 0),
    
    # Wayne's preference to avoid meetings before 14:00
    meeting_start >= 14 * 60,
    
    # Meeting must start within the working hours
    meeting_start >= start_time,
    meeting_start + meeting_duration <= end_time
]

# Create a solver instance
solver = Solver()

# Add all constraints to the solver
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