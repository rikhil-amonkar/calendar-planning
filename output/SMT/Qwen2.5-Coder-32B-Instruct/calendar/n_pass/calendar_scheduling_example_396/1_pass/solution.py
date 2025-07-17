from z3 import *

# Define the time slots in 30-minute increments from 9:00 to 17:00
time_slots = [900, 930, 1000, 1030, 1100, 1130, 1200, 1230, 1300, 1330, 1400, 1430, 1500, 1530, 1600, 1630, 1700]

# Define the participants and their busy times
participants = {
    "Andrea": [],
    "Jack": [900, 930, 1400, 1430],
    "Madison": [930, 1000, 1030, 1300, 1400, 1500, 1530, 1630, 1700],
    "Rachel": [930, 1000, 1030, 1100, 1130, 1200, 1230, 1300, 1330, 1430, 1500, 1530, 1600, 1630, 1700],
    "Douglas": [900, 930, 1000, 1030, 1100, 1130, 1200, 1230, 1300, 1330, 1400, 1430, 1500, 1530, 1600, 1630],
    "Ryan": [900, 930, 1300, 1400, 1430, 1500, 1530, 1600, 1630, 1700]
}

# Create a Z3 solver instance
solver = Solver()

# Define a variable for the start time of the meeting
start_time = Int('start_time')

# Add constraints for the meeting duration (30 minutes) and the work hours (9:00 to 17:00)
solver.add(start_time >= 900)
solver.add(start_time <= 1630)  # 16:30 is the latest start time for a 30-minute meeting to end by 17:00

# Add constraints for each participant's availability
for participant, busy_times in participants.items():
    for busy_time in busy_times:
        solver.add(Or(start_time != busy_time, start_time != busy_time - 30))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    start = model[start_time].as_long()
    end = start + 30
    start_time_str = f"{start // 100:02}:{start % 100:02}"
    end_time_str = f"{end // 100:02}:{end % 100:02}"
    print(f"SOLUTION:\nDay: Monday\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
else:
    print("No solution found")