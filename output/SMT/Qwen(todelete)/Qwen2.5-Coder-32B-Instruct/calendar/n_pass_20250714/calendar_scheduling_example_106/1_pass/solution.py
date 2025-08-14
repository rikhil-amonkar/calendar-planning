from z3 import *

# Define the variables for the meeting time
meeting_start = Int('meeting_start')
meeting_end = Int('meeting_end')

# Define the constraints for the meeting duration
s = Solver()
s.add(meeting_end == meeting_start + 60)  # Meeting duration is 1 hour

# Define the constraints for the work hours (9:00 to 17:00)
s.add(meeting_start >= 540)  # 9:00 in minutes from 00:00
s.add(meeting_end <= 1020)   # 17:00 in minutes from 00:00

# Define the constraints for each participant's availability
# Olivia: 12:30 to 13:30, 14:30 to 15:00, 16:30 to 17:00
s.add(Or(meeting_end <= 750, meeting_start >= 810))  # 12:30 to 13:30
s.add(Or(meeting_end <= 870, meeting_start >= 930))  # 14:30 to 15:00
s.add(Or(meeting_end <= 990, meeting_start >= 1020)) # 16:30 to 17:00

# Anna: No meetings the whole day, so no additional constraints

# Virginia: 9:00 to 10:00, 11:30 to 16:00, 16:30 to 17:00
s.add(Or(meeting_end <= 600, meeting_start >= 660))  # 9:00 to 10:00
s.add(Or(meeting_end <= 750, meeting_start >= 960))  # 11:30 to 16:00
s.add(Or(meeting_end <= 990, meeting_start >= 1020)) # 16:30 to 17:00

# Paul: 9:00 to 9:30, 11:00 to 11:30, 13:00 to 14:00, 14:30 to 16:00, 16:30 to 17:00
s.add(Or(meeting_end <= 570, meeting_start >= 570))  # 9:00 to 9:30
s.add(Or(meeting_end <= 690, meeting_start >= 720))  # 11:00 to 11:30
s.add(Or(meeting_end <= 780, meeting_start >= 840))  # 13:00 to 14:00
s.add(Or(meeting_end <= 870, meeting_start >= 930))  # 14:30 to 16:00
s.add(Or(meeting_end <= 990, meeting_start >= 1020)) # 16:30 to 17:00

# Check if there is a solution
if s.check() == sat:
    model = s.model()
    start_time_minutes = model[meeting_start].as_long()
    end_time_minutes = model[meeting_end].as_long()
    
    # Convert minutes to HH:MM format
    start_hour = start_time_minutes // 60
    start_minute = start_time_minutes % 60
    end_hour = end_time_minutes // 60
    end_minute = end_time_minutes % 60
    
    print(f"SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {start_hour:02}:{start_minute:02}")
    print(f"End Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found")