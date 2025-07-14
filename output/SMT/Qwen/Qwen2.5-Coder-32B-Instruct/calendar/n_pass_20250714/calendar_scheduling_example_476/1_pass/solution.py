from z3 import *

# Define the time slots in minutes from 9:00 to 17:00
start_time = 9 * 60  # 9:00 AM
end_time = 17 * 60   # 5:00 PM
meeting_duration = 30  # 30 minutes

# Create a variable for the start time of the meeting
meeting_start = Int('meeting_start')

# Define the constraints for each person
constraints = [
    # Daniel is free all day, so no additional constraints
    # Kathleen is busy from 14:30 to 15:30 (870 to 930 minutes)
    Or(meeting_start + meeting_duration <= 870, meeting_start >= 930),
    # Carolyn is busy from 12:00 to 12:30 (720 to 750 minutes) and 13:00 to 13:30 (780 to 810 minutes)
    Or(meeting_start + meeting_duration <= 720, meeting_start >= 750),
    Or(meeting_start + meeting_duration <= 780, meeting_start >= 810),
    # Roger is free all day, but prefers not to meet before 12:30 (750 minutes)
    meeting_start >= 750,
    # Cheryl is busy from 9:00 to 9:30 (540 to 570 minutes), 10:00 to 11:30 (600 to 690 minutes),
    # 12:30 to 13:30 (750 to 810 minutes), 14:00 to 17:00 (840 to 1020 minutes)
    Or(meeting_start + meeting_duration <= 540, meeting_start >= 570),
    Or(meeting_start + meeting_duration <= 600, meeting_start >= 690),
    Or(meeting_start + meeting_duration <= 750, meeting_start >= 810),
    Or(meeting_start + meeting_duration <= 840, meeting_start >= 1020),
    # Virginia is busy from 9:30 to 11:30 (570 to 690 minutes), 12:00 to 12:30 (720 to 750 minutes),
    # 13:00 to 13:30 (780 to 810 minutes), 14:30 to 15:30 (870 to 930 minutes), 16:00 to 17:00 (960 to 1020 minutes)
    Or(meeting_start + meeting_duration <= 570, meeting_start >= 690),
    Or(meeting_start + meeting_duration <= 720, meeting_start >= 750),
    Or(meeting_start + meeting_duration <= 780, meeting_start >= 810),
    Or(meeting_start + meeting_duration <= 870, meeting_start >= 930),
    Or(meeting_start + meeting_duration <= 960, meeting_start >= 1020),
    # Angela is busy from 9:30 to 10:00 (570 to 600 minutes), 10:30 to 11:30 (630 to 690 minutes),
    # 12:00 to 12:30 (720 to 750 minutes), 13:00 to 13:30 (780 to 810 minutes), 14:00 to 16:30 (840 to 990 minutes)
    Or(meeting_start + meeting_duration <= 570, meeting_start >= 600),
    Or(meeting_start + meeting_duration <= 630, meeting_start >= 690),
    Or(meeting_start + meeting_duration <= 720, meeting_start >= 750),
    Or(meeting_start + meeting_duration <= 780, meeting_start >= 810),
    Or(meeting_start + meeting_duration <= 840, meeting_start >= 990),
]

# Add constraints that the meeting must be within working hours
constraints.append(meeting_start >= start_time)
constraints.append(meeting_start + meeting_duration <= end_time)

# Create a solver instance and add the constraints
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_start_minutes = model[meeting_start].as_long()
    meeting_start_hour = meeting_start_minutes // 60
    meeting_start_minute = meeting_start_minutes % 60
    meeting_end_minutes = meeting_start_minutes + meeting_duration
    meeting_end_hour = meeting_end_minutes // 60
    meeting_end_minute = meeting_end_minutes % 60
    
    print("SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {meeting_start_hour:02}:{meeting_start_minute:02}")
    print(f"End Time: {meeting_end_hour:02}:{meeting_end_minute:02}")
else:
    print("No solution found.")