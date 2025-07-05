from z3 import *

# Define the time slots in minutes from 9:00 to 17:00
start_of_day = 9 * 60  # 9:00 AM
end_of_day = 17 * 60   # 5:00 PM

# Define the meeting duration in minutes
meeting_duration = 60  # 1 hour

# Define the time variable for the meeting start time
meeting_start = Int('meeting_start')

# Create a solver instance
solver = Solver()

# Add constraints for the meeting start time to be within working hours
solver.add(meeting_start >= start_of_day)
solver.add(meeting_start + meeting_duration <= end_of_day)

# Define the busy times for James and John
james_busy_times = [(11 * 60 + 30, 12 * 60), (14 * 60 + 30, 15 * 60)]
john_busy_times = [(9 * 60 + 30, 11 * 60), (11 * 60 + 30, 12 * 60), (12 * 60 + 30, 13 * 60), (14 * 60 + 30, 16 * 60)]

# Add constraints to avoid busy times
for start, end in james_busy_times:
    solver.add(Or(meeting_start + meeting_duration <= start, meeting_start >= end))

for start, end in john_busy_times:
    solver.add(Or(meeting_start + meeting_duration <= start, meeting_start >= end))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_start_time = model[meeting_start].as_long()
    meeting_end_time = meeting_start_time + meeting_duration
    
    # Convert the time back to HH:MM format
    def convert_to_hhmm(minutes):
        hours = minutes // 60
        minutes = minutes % 60
        return f"{hours:02}:{minutes:02}"
    
    print("SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {convert_to_hhmm(meeting_start_time)}")
    print(f"End Time: {convert_to_hhmm(meeting_end_time)}")
else:
    print("No solution found")