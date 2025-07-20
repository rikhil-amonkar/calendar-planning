from z3 import *

# Define the time slots in minutes from 9:00 to 17:00
start_time = 9 * 60  # 9:00 in minutes
end_time = 17 * 60   # 17:00 in minutes
meeting_duration = 60  # 1 hour meeting

# Define the participants
participants = ["Evelyn", "Joshua", "Kevin", "Gerald", "Jerry", "Jesse", "Kenneth"]

# Define the busy times for each participant
busy_times = {
    "Evelyn": [],
    "Joshua": [(11 * 60, 12 * 60 + 30), (13 * 60 + 30, 14 * 60 + 30), (16 * 60 + 30, 17 * 60)],
    "Kevin": [],
    "Gerald": [],
    "Jerry": [(9 * 60, 9 * 60 + 30), (10 * 60 + 30, 12 * 60), (12 * 60 + 30, 13 * 60), 
              (13 * 60 + 30, 14 * 60), (14 * 60 + 30, 15 * 60), (15 * 60 + 30, 16 * 60)],
    "Jesse": [(9 * 60, 9 * 60 + 30), (10 * 60 + 30, 12 * 60), (12 * 60 + 30, 13 * 60), 
              (14 * 60 + 30, 15 * 60), (15 * 60 + 30, 16 * 60)],
    "Kenneth": [(10 * 60 + 30, 12 * 60 + 30), (13 * 60 + 30, 14 * 60), (14 * 60 + 30, 15 * 60), 
                (15 * 60 + 30, 16 * 60), (16 * 60 + 30, 17 * 60)]
}

# Create a Z3 solver
solver = Solver()

# Define the start time of the meeting as a Z3 integer variable
meeting_start = Int('meeting_start')

# Add constraints for the meeting start time
solver.add(meeting_start >= start_time)
solver.add(meeting_start <= end_time - meeting_duration)

# Add constraints to ensure the meeting does not overlap with busy times
for participant, times in busy_times.items():
    for start, end in times:
        solver.add(Or(meeting_start + meeting_duration <= start, meeting_start >= end))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_start_minutes = model[meeting_start].as_long()
    meeting_start_time = f"{meeting_start_minutes // 60:02}:{meeting_start_minutes % 60:02}"
    meeting_end_time = f"{(meeting_start_minutes + meeting_duration) // 60:02}:{(meeting_start_minutes + meeting_duration) % 60:02}"
    print(f"SOLUTION:\nDay: Monday\nStart Time: {meeting_start_time}\nEnd Time: {meeting_end_time}")
else:
    print("No solution found")