from z3 import *

# Define the time slots in minutes from 9:00 to 17:00
start_time = 9 * 60  # 9:00 AM
end_time = 17 * 60   # 5:00 PM
meeting_duration = 30  # 30 minutes

# Create a Z3 solver instance
solver = Solver()

# Define the start time variable for the meeting
meeting_start = Int('meeting_start')

# Add constraints for the meeting time to be within working hours
solver.add(meeting_start >= start_time)
solver.add(meeting_start + meeting_duration <= end_time)

# Define the busy times for each participant
busy_times = {
    'Raymond': [(9*60, 9*60+30), (11*60+30, 12*60), (13*60, 13*60+30), (15*60, 15*60+30)],
    'Billy': [(10*60, 10*60+30), (12*60, 13*60), (16*60+30, 17*60)],
    'Donald': [(9*60, 9*60+30), (10*60, 11*60), (12*60, 13*60), (14*60, 14*60+30), (16*60, 17*60)]
}

# Add constraints to avoid busy times
for person, times in busy_times.items():
    for start, end in times:
        solver.add(Or(meeting_start + meeting_duration <= start, meeting_start >= end))

# Billy's preference to avoid meetings after 15:00
solver.add(meeting_start + meeting_duration <= 15*60)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_start_value = model[meeting_start].as_long()
    meeting_start_time = f"{meeting_start_value // 60:02}:{meeting_start_value % 60:02}"
    meeting_end_time = f"{(meeting_start_value + meeting_duration) // 60:02}:{(meeting_start_value + meeting_duration) % 60:02}"
    print("SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {meeting_start_time}")
    print(f"End Time: {meeting_end_time}")
else:
    print("No solution found.")