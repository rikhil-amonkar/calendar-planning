from z3 import *

# Define the time slots in 30-minute increments from 9:00 to 17:00
time_slots = [900, 930, 1000, 1030, 1100, 1130, 1200, 1230, 1300, 1330, 1400, 1430, 1500, 1530, 1600, 1630]

# Define the participants
participants = ['Ronald', 'Stephen', 'Brittany', 'Dorothy', 'Rebecca', 'Jordan']

# Define the blocked time slots for each participant
blocked_slots = {
    'Ronald': [],
    'Stephen': [1000, 1030, 1200, 1230],
    'Brittany': [1100, 1130, 1330, 1400, 1530, 1600, 1630],
    'Dorothy': [900, 930, 1000, 1030, 1100, 1200, 1230, 1300, 1330, 1400, 1500, 1530, 1600, 1630],
    'Rebecca': [930, 1000, 1030, 1100, 1130, 1200, 1230, 1300, 1330, 1400, 1430, 1500, 1530, 1600, 1630],
    'Jordan': [900, 930, 1000, 1030, 1100, 1130, 1200, 1300, 1330, 1400, 1430, 1500, 1530, 1600, 1630]
}

# Create a Z3 solver instance
solver = Solver()

# Define a boolean variable for each time slot indicating if the meeting can be scheduled at that time
meeting_start = Int('meeting_start')

# Add constraints that the meeting start time must be within the working hours and in 30-minute increments
solver.add(meeting_start >= 900)
solver.add(meeting_start <= 1630)
solver.add(Or([meeting_start == t for t in time_slots]))

# Define the meeting duration (30 minutes)
meeting_duration = 30

# Add constraints that the meeting time does not overlap with any blocked time slots for any participant
for participant in participants:
    for blocked_time in blocked_slots[participant]:
        solver.add(meeting_start != blocked_time)
        solver.add(meeting_start + meeting_duration <= blocked_time + 30)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + meeting_duration
    start_time_str = f"{start_time // 100:02}:{start_time % 100:02}"
    end_time_str = f"{end_time // 100:02}:{end_time % 100:02}"
    print(f"SOLUTION:\nDay: Monday\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
else:
    print("No solution found")