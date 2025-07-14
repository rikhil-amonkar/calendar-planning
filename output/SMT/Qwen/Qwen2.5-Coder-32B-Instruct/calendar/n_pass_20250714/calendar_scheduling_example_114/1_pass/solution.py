from z3 import *

# Define the time slots in minutes from 9:00 to 17:00
start_time = 9 * 60
end_time = 17 * 60

# Define the meeting duration in minutes
meeting_duration = 60

# Define the participants and their busy times in minutes from 9:00
busy_times = {
    "Stephanie": [(10 * 60, 10 * 60 + 30), (16 * 60, 16 * 60 + 30)],
    "Cheryl": [(10 * 60, 10 * 60 + 30), (11 * 60 + 30, 12 * 60), (13 * 60 + 30, 14 * 60), (16 * 60 + 30, 17 * 60)],
    "Bradley": [(9 * 60 + 30, 10 * 60), (10 * 60 + 30, 11 * 60 + 30), (13 * 60 + 30, 14 * 60), (14 * 60 + 30, 15 * 60), (15 * 60 + 30, 17 * 60)],
    "Steven": [(9 * 60, 12 * 60), (13 * 60, 13 * 60 + 30), (14 * 60 + 30, 17 * 60)]
}

# Create a Z3 solver instance
solver = Solver()

# Define the start time variable for the meeting
meeting_start = Int('meeting_start')

# Add constraints for the meeting start time
solver.add(meeting_start >= start_time)
solver.add(meeting_start <= end_time - meeting_duration)

# Add constraints for each participant's busy times
for person, times in busy_times.items():
    for start, end in times:
        solver.add(Or(meeting_start + meeting_duration <= start, meeting_start >= end))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_start_value = model[meeting_start].as_long()
    meeting_end_value = meeting_start_value + meeting_duration
    
    # Convert the meeting start and end times back to HH:MM format
    meeting_start_time = f"{meeting_start_value // 60:02}:{meeting_start_value % 60:02}"
    meeting_end_time = f"{meeting_end_value // 60:02}:{meeting_end_value % 60:02}"
    
    # Print the solution
    print("SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {meeting_start_time}")
    print(f"End Time: {meeting_end_time}")
else:
    print("No solution found.")