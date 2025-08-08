from z3 import *

# Define the time slots in minutes from 9:00 to 17:00
start_time = 9 * 60  # 9:00 in minutes
end_time = 17 * 60   # 17:00 in minutes
meeting_duration = 30  # 30 minutes

# Define the meeting start time as a Z3 integer variable
meeting_start = Int('meeting_start')

# Define the constraints for each participant
constraints = [
    # Christine is busy on Monday during 9:30 to 10:30, 12:00 to 12:30, 13:00 to 13:30, 14:30 to 15:00, 16:00 to 16:30
    Or(meeting_start < 9*60 + 30, meeting_start + meeting_duration > 10*60 + 30),
    Or(meeting_start < 12*60, meeting_start + meeting_duration > 12*60 + 30),
    Or(meeting_start < 13*60, meeting_start + meeting_duration > 13*60 + 30),
    Or(meeting_start < 14*60 + 30, meeting_start + meeting_duration > 15*60),
    Or(meeting_start < 16*60, meeting_start + meeting_duration > 16*60 + 30),

    # Bobby is busy on Monday during 12:00 to 12:30, 14:30 to 15:00
    Or(meeting_start < 12*60, meeting_start + meeting_duration > 12*60 + 30),
    Or(meeting_start < 14*60 + 30, meeting_start + meeting_duration > 15*60),

    # Elizabeth is busy on Monday during 9:00 to 9:30, 11:30 to 13:00, 13:30 to 14:00, 15:00 to 15:30, 16:00 to 17:00
    Or(meeting_start < 9*60, meeting_start + meeting_duration > 9*60 + 30),
    Or(meeting_start < 11*60 + 30, meeting_start + meeting_duration > 13*60),
    Or(meeting_start < 13*60 + 30, meeting_start + meeting_duration > 14*60),
    Or(meeting_start < 15*60, meeting_start + meeting_duration > 15*60 + 30),
    Or(meeting_start < 16*60, meeting_start + meeting_duration > 17*60),

    # Tyler is busy on Monday during 9:00 to 11:00, 12:00 to 12:30, 13:00 to 13:30, 15:30 to 16:00, 16:30 to 17:00
    Or(meeting_start < 9*60, meeting_start + meeting_duration > 11*60),
    Or(meeting_start < 12*60, meeting_start + meeting_duration > 12*60 + 30),
    Or(meeting_start < 13*60, meeting_start + meeting_duration > 13*60 + 30),
    Or(meeting_start < 15*60 + 30, meeting_start + meeting_duration > 16*60),
    Or(meeting_start < 16*60 + 30, meeting_start + meeting_duration > 17*60),

    # Edward is busy on Monday during 9:00 to 9:30, 10:00 to 11:00, 11:30 to 14:00, 14:30 to 15:30, 16:00 to 17:00
    Or(meeting_start < 9*60, meeting_start + meeting_duration > 9*60 + 30),
    Or(meeting_start < 10*60, meeting_start + meeting_duration > 11*60),
    Or(meeting_start < 11*60 + 30, meeting_start + meeting_duration > 14*60),
    Or(meeting_start < 14*60 + 30, meeting_start + meeting_duration > 15*60 + 30),
    Or(meeting_start < 16*60, meeting_start + meeting_duration > 17*60),

    # Janice would rather not meet on Monday after 13:00
    meeting_start < 13*60,

    # Ensure the meeting does not overlap with Tyler's busy period from 9:00 to 11:00
    Or(meeting_start < 9*60, meeting_start + meeting_duration > 11*60)
]

# Add constraints that the meeting must be within work hours
constraints.append(meeting_start >= start_time)
constraints.append(meeting_start + meeting_duration <= end_time)

# Create a solver and add the constraints
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