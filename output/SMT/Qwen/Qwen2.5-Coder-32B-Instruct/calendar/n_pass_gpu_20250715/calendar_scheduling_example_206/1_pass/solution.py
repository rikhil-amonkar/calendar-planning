from z3 import *

# Define the variables for the meeting start time
meeting_start = Int('meeting_start')

# Constraints
constraints = [
    # Meeting duration is 30 minutes
    meeting_start >= 9 * 60,  # 9:00 in minutes
    meeting_start + 30 <= 17 * 60,  # 17:00 in minutes
    
    # Shirley's availability
    Or(meeting_start < 10 * 60 + 30, meeting_start + 30 > 11 * 60),  # Not 10:30 - 11:00
    Or(meeting_start < 12 * 60, meeting_start + 30 > 12 * 60 + 30),  # Not 12:00 - 12:30
    
    # Jacob's availability
    Or(meeting_start < 9 * 60 + 30, meeting_start + 30 > 10 * 60),  # Not 9:00 - 9:30
    Or(meeting_start < 10 * 60, meeting_start + 30 > 10 * 60 + 30),  # Not 10:00 - 10:30
    Or(meeting_start < 11 * 60, meeting_start + 30 > 11 * 60 + 30),  # Not 11:00 - 11:30
    Or(meeting_start < 12 * 60 + 30, meeting_start + 30 > 13 * 60 + 30),  # Not 12:30 - 13:30
    Or(meeting_start < 14 * 60 + 30, meeting_start + 30 > 15 * 60),  # Not 14:30 - 15:00
    
    # Stephen's availability
    Or(meeting_start < 11 * 60 + 30, meeting_start + 30 > 12 * 60),  # Not 11:30 - 12:00
    Or(meeting_start < 12 * 60 + 30, meeting_start + 30 > 13 * 60),  # Not 12:30 - 13:00
    
    # Margaret's availability
    Or(meeting_start < 9 * 60 + 30, meeting_start + 30 > 10 * 60 + 30),  # Not 9:00 - 9:30
    Or(meeting_start < 10 * 60 + 30, meeting_start + 30 > 12 * 60 + 30),  # Not 10:30 - 12:30
    Or(meeting_start < 13 * 60, meeting_start + 30 > 13 * 60 + 30),  # Not 13:00 - 13:30
    Or(meeting_start < 15 * 60, meeting_start + 30 > 15 * 60 + 30),  # Not 15:00 - 15:30
    Or(meeting_start < 16 * 60 + 30, meeting_start + 30 > 17 * 60),  # Not 16:30 - 17:00
    
    # Mason's availability
    Or(meeting_start < 10 * 60, meeting_start + 30 > 10 * 60),  # Not 9:00 - 10:00
    Or(meeting_start < 10 * 60 + 30, meeting_start + 30 > 11 * 60),  # Not 10:30 - 11:00
    Or(meeting_start < 11 * 60 + 30, meeting_start + 30 > 12 * 60 + 30),  # Not 11:30 - 12:30
    Or(meeting_start < 13 * 60, meeting_start + 30 > 13 * 60 + 30),  # Not 13:00 - 13:30
    Or(meeting_start < 14 * 60, meeting_start + 30 > 14 * 60 + 30),  # Not 14:00 - 14:30
    Or(meeting_start < 16 * 60 + 30, meeting_start + 30 > 17 * 60),  # Not 16:30 - 17:00
    
    # Margaret's preference
    meeting_start >= 14 * 60 + 30  # After 14:30
]

# Solve the constraints
solver = Solver()
solver.add(constraints)

if solver.check() == sat:
    model = solver.model()
    meeting_start_time = model[meeting_start].as_long()
    meeting_end_time = meeting_start_time + 30
    
    def format_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02}:{mins:02}"
    
    print("SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {format_time(meeting_start_time)}")
    print(f"End Time: {format_time(meeting_end_time)}")
else:
    print("No solution found")