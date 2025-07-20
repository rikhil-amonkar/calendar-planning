from z3 import *

# Define the time slots in 30-minute increments from 9:00 to 17:00
time_slots = [900, 930, 1000, 1030, 1100, 1130, 1200, 1230, 1300, 1330, 1400, 1430, 1500, 1530, 1600, 1630]

# Define the meeting duration in 30-minute increments
meeting_duration = 1

# Define the participants
participants = ["Megan", "Christine", "Gabriel", "Sara", "Bruce", "Kathryn", "Billy"]

# Define the constraints for each participant
constraints = {
    "Megan": [(900, 930), (1000, 1100), (1200, 1230)],
    "Christine": [(900, 930), (1130, 1200), (1300, 1400), (1530, 1630)],
    "Gabriel": [],
    "Sara": [(1130, 1200), (1430, 1500)],
    "Bruce": [(930, 1000), (1030, 1200), (1230, 1400), (1430, 1500), (1530, 1630)],
    "Kathryn": [(1000, 1530), (1600, 1630)],
    "Billy": [(900, 930), (1100, 1130), (1200, 1400), (1430, 1500)]
}

# Create a Z3 solver
solver = Solver()

# Define a variable for the start time of the meeting
start_time = Int('start_time')

# Add constraints to the solver
# The meeting must start and end within the work hours
solver.add(start_time >= 900)
solver.add(start_time + meeting_duration * 30 <= 1700)

# The meeting must not overlap with any busy times for any participant
for participant, busy_times in constraints.items():
    for busy_start, busy_end in busy_times:
        solver.add(Or(start_time + meeting_duration * 30 <= busy_start, start_time >= busy_end))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    start = model[start_time].as_long()
    end = start + meeting_duration * 30
    start_time_str = f"{start // 100:02}:{start % 100:02}"
    end_time_str = f"{end // 100:02}:{end % 100:02}"
    # Ensure the end time is within the valid range
    if end % 100 >= 60:
        end_time_str = f"{(end // 100) + 1:02}:{end % 100 - 60:02}"
    print(f"SOLUTION:\nDay: Monday\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
else:
    print("No solution found")