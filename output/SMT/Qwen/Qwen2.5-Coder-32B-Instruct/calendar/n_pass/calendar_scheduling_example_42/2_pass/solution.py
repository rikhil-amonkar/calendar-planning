from z3 import *

# Define the time slots as integers representing minutes from 9:00
start_time = 9 * 60  # 9:00 AM
end_time = 17 * 60   # 5:00 PM
meeting_duration = 60  # 1 hour

# Define the meeting start time variable
meeting_start = Int('meeting_start')

# Define the constraints for each person
julie_busy = [(9*60, 9*60+30), (11*60, 11*60+30), (12*60, 12*60+30), (13*60+30, 14*60), (16*60, 17*60)]
sean_busy = [(9*60, 9*60+30), (13*60, 13*60+30), (15*60, 15*60+30), (16*60, 16*60+30)]
lori_busy = [(10*60, 10*60+30), (11*60, 13*60), (15*60+30, 17*60)]

# Combine all busy times into a single list of tuples
busy_times = julie_busy + sean_busy + lori_busy

# Create the solver
solver = Solver()

# Add constraint that the meeting must fit within the working hours
solver.add(meeting_start >= start_time)
solver.add(meeting_start + meeting_duration <= end_time)

# Add constraints for each person's busy times
for start, end in busy_times:
    solver.add(Or(meeting_start + meeting_duration <= start, meeting_start >= end))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_start_minutes = model[meeting_start].as_long()
    meeting_start_time = f"{meeting_start_minutes // 60}:{meeting_start_minutes % 60:02}"
    meeting_end_time = f"{(meeting_start_minutes + meeting_duration) // 60}:{(meeting_start_minutes + meeting_duration) % 60:02}"
    print(f"SOLUTION:\nDay: Monday\nStart Time: {meeting_start_time}\nEnd Time: {meeting_end_time}")
else:
    print("No solution found")