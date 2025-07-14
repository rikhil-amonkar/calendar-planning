from z3 import *

# Define the time slots in minutes from 9:00 to 17:00 (480 minutes)
start_of_day = 480  # 9:00 in minutes
end_of_day = 1020   # 17:00 in minutes
meeting_duration = 30

# Create a solver instance
solver = Solver()

# Define variables for the start time of the meeting
meeting_start = Int('meeting_start')

# Add constraints for the meeting time
solver.add(meeting_start >= start_of_day)
solver.add(meeting_start + meeting_duration <= end_of_day)

# Define the busy times for each participant
busy_times = {
    'Wayne': [],
    'Melissa': [(600, 660), (750, 840), (900, 930)],  # 10:00-11:00, 12:30-14:00, 15:00-15:30
    'Catherine': [],
    'Gregory': [(750, 780), (930, 990)],             # 12:30-13:00, 15:30-16:00
    'Victoria': [(540, 570), (630, 720), (780, 840), (870, 930), (990, 1050)],  # 9:30-10:30, 10:30-11:30, 13:00-14:00, 14:30-15:00, 15:30-16:30
    'Thomas': [(600, 720), (750, 780), (870, 960)],    # 10:00-12:00, 12:30-13:00, 14:30-16:00
    'Jennifer': [(540, 570), (600, 630), (660, 780), (810, 870), (900, 930), (960, 1020)]  # 9:00-9:30, 10:00-10:30, 11:00-13:00, 13:30-14:30, 15:00-15:30, 16:00-16:30
}

# Add constraints to avoid busy times
for person, times in busy_times.items():
    for start, end in times:
        solver.add(Or(meeting_start + meeting_duration <= start, meeting_start >= end))
        print(f"Added constraint for {person} from {start} to {end}")

# Wayne's preference to avoid meetings before 14:00
wayne_preference_start = 840  # 14:00 in minutes
solver.add(meeting_start >= wayne_preference_start)
print(f"Added Wayne's preference constraint from {wayne_preference_start}")

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_start_minutes = model[meeting_start].as_long()
    meeting_start_time = f"{(meeting_start_minutes // 60):02}:{(meeting_start_minutes % 60):02}"
    meeting_end_time = f"{((meeting_start_minutes + meeting_duration) // 60):02}:{((meeting_start_minutes + meeting_duration) % 60):02}"
    solution = f"SOLUTION:\nDay: Monday\nStart Time: {meeting_start_time}\nEnd Time: {meeting_end_time}"
    print(solution)
else:
    print("No solution found")