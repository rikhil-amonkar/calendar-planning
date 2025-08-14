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

# Define a variable for the start time of the meeting
start_time = Int('start_time')

# Add constraints to ensure the meeting is within work hours and is 30 minutes long
solver.add(start_time >= 900)
solver.add(start_time <= 1630)  # 16:30 is the latest start time for a 30-minute meeting to end by 17:00

# Add constraints for each participant's availability
for participant, busy_slots in constraints.items():
    for start, end in busy_slots:
        solver.add(Or(start_time < start, start_time + 30 > end))

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