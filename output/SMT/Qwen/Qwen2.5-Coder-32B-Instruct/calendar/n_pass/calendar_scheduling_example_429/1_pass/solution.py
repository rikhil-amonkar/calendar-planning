from z3 import *

# Define the time slots in minutes from 9:00 to 17:00
start_time = 9 * 60  # 9:00 in minutes
end_time = 17 * 60   # 17:00 in minutes
meeting_duration = 30  # 30 minutes

# Define the participants and their busy times
participants = {
    "Judy": [(13*60, 13*60+30), (16*60, 16*60+30)],
    "Olivia": [(10*60, 10*60+30), (12*60, 13*60), (14*60, 14*60+30)],
    "Eric": [],
    "Jacqueline": [(10*60, 10*60+30), (15*60, 15*60+30)],
    "Laura": [(9*60, 10*60), (10*60+30, 12*60), (13*60, 13*60+30), (14*30, 15*60), (15*30, 17*60)],
    "Tyler": [(9*60, 10*60), (11*60, 11*60+30), (12*30, 13*60), (14*60, 14*60+30), (15*30, 17*60)],
    "Lisa": [(9*60+30, 10*60+30), (11*60, 11*60+30), (12*60, 12*60+30), (13*60, 13*60+30), (14*60, 14*60+30), (16*60, 17*60)]
}

# Create a solver instance
solver = Solver()

# Define the start time of the meeting as a variable
meeting_start = Int('meeting_start')

# Add constraints for the meeting start time
solver.add(meeting_start >= start_time)
solver.add(meeting_start <= end_time - meeting_duration)

# Add constraints for each participant's availability
for participant, busy_times in participants.items():
    for start, end in busy_times:
        solver.add(Or(meeting_start + meeting_duration <= start, meeting_start >= end))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_start_minutes = model[meeting_start].as_long()
    meeting_start_time = f"{meeting_start_minutes // 60:02}:{meeting_start_minutes % 60:02}"
    meeting_end_time = f"{(meeting_start_minutes + meeting_duration) // 60:02}:{(meeting_start_minutes + meeting_duration) % 60:02}"
    print("SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {meeting_start_time}")
    print(f"End Time: {meeting_end_time}")
else:
    print("No solution found")