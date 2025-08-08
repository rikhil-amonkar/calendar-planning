from z3 import *

# Define the time slots in 30-minute increments from 9:00 to 17:00
time_slots = [900, 930, 1000, 1030, 1100, 1130, 1200, 1230, 1300, 1330, 1400, 1430, 1500, 1530, 1600, 1630]

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
    "Billy": [(900, 930), (1100, 1130), (1200, 1400), (1430, 1530)]
}

# Create a Z3 solver
solver = Solver()

# Define a variable for the start time of the meeting
start_time = Int('start_time')

# Add constraints to ensure the meeting is within work hours and is 30 minutes long
solver.add(start_time >= 900)
solver.add(start_time <= 1630)
solver.add(Or([start_time == t for t in time_slots]))

# Add constraints for each participant's availability
for participant, busy_slots in constraints.items():
    for busy_start, busy_end in busy_slots:
        solver.add(Or(start_time < busy_start, start_time + 30 > busy_end))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    start = model[start_time].as_long()
    end = start + 30
    # Convert start and end times to HH:MM format
    start_time_str = f"{start // 100:02}:{start % 100:02}"
    end_hour = end // 100
    end_minute = end % 100
    if end_minute == 60:
        end_hour += 1
        end_minute = 0
    end_time_str = f"{end_hour:02}:{end_minute:02}"
    print(f"SOLUTION:\nDay: Monday\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
else:
    print("No solution found")