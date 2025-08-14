from z3 import *

# Define the time slots in minutes from 9:00 to 17:00
start_time = 9 * 60
end_time = 17 * 60
meeting_duration = 30

# Define the participants and their blocked times
participants = {
    "Ronald": [],
    "Stephen": [(10*60, 10*60+30), (12*60, 12*60+30)],
    "Brittany": [(11*60, 11*60+30), (13*60+30, 14*60), (15*60+30, 16*60), (16*60+30, 17*60)],
    "Dorothy": [(9*60, 9*60+30), (10*60, 10*60+30), (11*60, 12*60+30), (13*60, 15*60), (15*60+30, 17*60)],
    "Rebecca": [(9*60+30, 10*60+30), (11*60, 11*60+30), (12*60, 12*60+30), (13*60, 17*60)],
    "Jordan": [(9*60, 9*60+30), (10*60, 11*60), (11*60+30, 12*60), (13*60, 15*60), (15*60+30, 16*60+30)]
}

# Create a solver instance
solver = Solver()

# Define the variable for the start time of the meeting
meeting_start = Int('meeting_start')

# Add constraints for the meeting start time
solver.add(meeting_start >= start_time)
solver.add(meeting_start + meeting_duration <= end_time)

# Add constraints for each participant's availability
for participant, blocks in participants.items():
    for block_start, block_end in blocks:
        # The meeting should not overlap with any blocked time
        solver.add(Or(meeting_start + meeting_duration <= block_start, meeting_start >= block_end))

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
    print("No solution found")