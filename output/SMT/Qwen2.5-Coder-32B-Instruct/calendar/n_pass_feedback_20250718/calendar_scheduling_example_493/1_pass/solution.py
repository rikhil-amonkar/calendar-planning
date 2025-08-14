from z3 import *

# Define the time slots in 30-minute increments from 9:00 to 17:00
time_slots = [900, 930, 1000, 1030, 1100, 1130, 1200, 1230, 1300, 1330, 1400, 1430, 1500, 1530, 1600, 1630, 1700]

# Create a Z3 solver instance
solver = Solver()

# Define a boolean variable for each time slot indicating if the meeting can be scheduled at that time
meeting_time = Int('meeting_time')

# Define the constraints for each participant
constraints = [
    # Tyler is free the entire day
    # Kelly has no meetings the whole day
    # Stephanie has blocked their calendar on Monday during 11:00 to 11:30, 14:30 to 15:00
    And(meeting_time != 1100, meeting_time != 1130, meeting_time != 1430, meeting_time != 1500),
    # Hannah has no meetings the whole day
    # Joe has blocked their calendar on Monday during 9:00 to 9:30, 10:00 to 12:00, 12:30 to 13:00, 14:00 to 17:00
    And(meeting_time != 900, meeting_time != 930, meeting_time != 1000, meeting_time != 1030, meeting_time != 1100, meeting_time != 1130, meeting_time != 1200, meeting_time != 1230, meeting_time != 1300, meeting_time != 1400, meeting_time != 1430, meeting_time != 1500, meeting_time != 1530, meeting_time != 1600, meeting_time != 1630, meeting_time != 1700),
    # Diana has meetings on Monday during 9:00 to 10:30, 11:30 to 12:00, 13:00 to 14:00, 14:30 to 15:30, 16:00 to 17:00
    And(meeting_time != 900, meeting_time != 930, meeting_time != 1000, meeting_time != 1030, meeting_time != 1130, meeting_time != 1200, meeting_time != 1300, meeting_time != 1330, meeting_time != 1400, meeting_time != 1430, meeting_time != 1500, meeting_time != 1530, meeting_time != 1600, meeting_time != 1630, meeting_time != 1700),
    # Deborah is busy on Monday during 9:00 to 10:00, 10:30 to 12:00, 12:30 to 13:00, 13:30 to 14:00, 14:30 to 15:30, 16:00 to 16:30
    And(meeting_time != 900, meeting_time != 930, meeting_time != 1000, meeting_time != 1030, meeting_time != 1100, meeting_time != 1130, meeting_time != 1200, meeting_time != 1230, meeting_time != 1300, meeting_time != 1330, meeting_time != 1400, meeting_time != 1430, meeting_time != 1500, meeting_time != 1530, meeting_time != 1600, meeting_time != 1630)
]

# Add constraints to the solver
for constraint in constraints:
    solver.add(constraint)

# Define the meeting duration (30 minutes)
meeting_duration = 30

# Add constraint that the meeting must start and end within the work hours
solver.add(meeting_time >= 900)
solver.add(meeting_time + meeting_duration <= 1700)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    start_time = model[meeting_time].as_long()
    end_time = start_time + meeting_duration
    print(f"SOLUTION:\nDay: Monday\nStart Time: {start_time // 100:02}:{start_time % 100:02}\nEnd Time: {end_time // 100:02}:{end_time % 100:02}")
else:
    print("No solution found")