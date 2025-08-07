from z3 import *

# Define the time slots in 30-minute increments from 9:00 to 17:00
time_slots = [900, 930, 1000, 1030, 1100, 1130, 1200, 1230, 1300, 1330, 1400, 1430, 1500, 1530, 1600, 1630]

# Create a Z3 solver instance
solver = Solver()

# Define a variable for the meeting start time
meeting_start = Int('meeting_start')

# Define the constraints for each participant
constraints = [
    # Tyler is free the entire day
    # Kelly has no meetings the whole day
    # Stephanie has blocked their calendar on Monday during 11:00 to 11:30, 14:30 to 15:00
    And(meeting_start != 1100, meeting_start != 1430),
    # Hannah has no meetings the whole day
    # Joe has blocked their calendar on Monday during 9:00 to 9:30, 10:00 to 12:00, 12:30 to 13:00, 14:00 to 17:00
    And(meeting_start != 900, meeting_start != 1000, meeting_start != 1200, meeting_start != 1400),
    # Diana has meetings on Monday during 9:00 to 10:30, 11:30 to 12:00, 13:00 to 14:00, 14:30 to 15:30, 16:00 to 17:00
    And(meeting_start != 900, meeting_start != 1000, meeting_start != 1130, meeting_start != 1300, meeting_start != 1430, meeting_start != 1600),
    # Deborah is busy on Monday during 9:00 to 10:00, 10:30 to 12:00, 12:30 to 13:00, 13:30 to 14:00, 14:30 to 15:30, 16:00 to 16:30
    And(meeting_start != 900, meeting_start != 1000, meeting_start != 1100, meeting_start != 1200, meeting_start != 1300, meeting_start != 1330, meeting_start != 1400, meeting_start != 1430, meeting_start != 1500, meeting_start != 1600)
]

# Add constraints to the solver
for constraint in constraints:
    solver.add(constraint)

# Define the meeting duration (30 minutes)
meeting_duration = 30

# Add constraint that the meeting must start and end within the work hours and be 30 minutes long
solver.add(And(meeting_start >= 900, meeting_start <= 1630))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + meeting_duration
    print(f"SOLUTION:\nDay: Monday\nStart Time: {start_time // 100:02}:{start_time % 100:02}\nEnd Time: {end_time // 100:02}:{end_time % 100:02}")
else:
    print("No solution found")