from z3 import *

# Define the time slots in 30-minute increments from 9:00 to 17:00
time_slots = [900, 930, 1000, 1030, 1100, 1130, 1200, 1230, 1300, 1330, 1400, 1430, 1500, 1530, 1600, 1630, 1700]

# Define the participants
participants = ["Gregory", "Jonathan", "Barbara", "Jesse", "Alan", "Nicole", "Catherine"]

# Define the constraints for each participant
constraints = {
    "Gregory": [(900, 930), (1130, 1200)],
    "Jonathan": [(900, 930), (1200, 1230), (1300, 1330), (1500, 1600), (1630, 1700)],
    "Barbara": [(1000, 1030), (1330, 1400)],
    "Jesse": [(1000, 1100), (1230, 1430)],
    "Alan": [(930, 1100), (1130, 1230), (1300, 1530), (1600, 1700)],
    "Nicole": [(900, 1030), (1130, 1200), (1230, 1330), (1400, 1700)],
    "Catherine": [(900, 1030), (1200, 1330), (1500, 1530), (1600, 1630)]
}

# Create a Z3 solver
solver = Solver()

# Define a variable for the meeting start time
meeting_start = Int('meeting_start')

# Define the meeting duration (30 minutes)
meeting_duration = 30

# Define the meeting end time
meeting_end = meeting_start + meeting_duration

# Add constraints for the meeting to be within work hours
solver.add(meeting_start >= 900)
solver.add(meeting_end <= 1700)

# Add constraints for each participant's availability
for participant, busy_slots in constraints.items():
    for start, end in busy_slots:
        # The meeting should not overlap with any busy slot
        solver.add(Or(meeting_end <= start, meeting_start >= end))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + meeting_duration
    print("SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {start_time // 100:02}:{start_time % 100:02}")
    print(f"End Time: {end_time // 100:02}:{end_time % 100:02}")
else:
    print("No solution found")