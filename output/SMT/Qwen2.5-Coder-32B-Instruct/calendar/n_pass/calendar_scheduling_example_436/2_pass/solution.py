from z3 import *

# Define the time slots in 30-minute increments from 9:00 to 17:00
time_slots = [900, 930, 1000, 1030, 1100, 1130, 1200, 1230, 1300, 1330, 1400, 1430, 1500, 1530, 1600, 1630]

# Define the meeting duration in 30-minute increments
meeting_duration = 1

# Define the participants and their busy times
participants = {
    'Patrick': [(1330, 1400), (1430, 1500)],
    'Shirley': [(900, 930), (1100, 1130), (1200, 1230), (1430, 1500), (1600, 1700)],
    'Jeffrey': [(900, 930), (1030, 1100), (1130, 1200), (1300, 1330), (1600, 1700)],
    'Gloria': [(1130, 1200), (1500, 1530)],
    'Nathan': [(900, 930), (1030, 1200), (1400, 1700)],
    'Angela': [(900, 930), (1000, 1100), (1230, 1500), (1530, 1630)],
    'David': [(900, 930), (1000, 1030), (1100, 1400), (1430, 1630)]
}

# Create a Z3 solver
solver = Solver()

# Define a variable for the start time of the meeting
start_time = Int('start_time')

# Add constraints for the meeting to be within work hours and of the correct duration
solver.add(start_time >= 900)
solver.add(start_time + meeting_duration * 30 <= 1700)

# Add constraints for each participant's availability
for participant, busy_times in participants.items():
    for busy_start, busy_end in busy_times:
        # The meeting should not overlap with any busy time
        solver.add(Or(start_time + meeting_duration * 30 <= busy_start, start_time >= busy_end))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    start = model[start_time].as_long()
    end = start + meeting_duration * 30
    start_time_str = f"{start // 100:02}:{start % 100:02}"
    end_time_str = f"{end // 100:02}:{end % 100:02}"
    print(f"SOLUTION:\nDay: Monday\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
else:
    print("No solution found")