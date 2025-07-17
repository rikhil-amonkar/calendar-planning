from z3 import *

# Define the time slots in 30-minute increments from 9:00 to 17:00
time_slots = [900, 930, 1000, 1030, 1100, 1130, 1200, 1230, 1300, 1330, 1400, 1430, 1500, 1530, 1600, 1630]

# Define the participants and their busy times
participants = {
    "Katherine": [(1200, 1230), (1300, 1430)],
    "Rebecca": [],
    "Julie": [(900, 930), (1030, 1100), (1330, 1400), (1500, 1530)],
    "Angela": [(900, 1000), (1030, 1100), (1130, 1400), (1430, 1500), (1630, 1700)],
    "Nicholas": [(930, 1100), (1130, 1330), (1400, 1600), (1630, 1700)],
    "Carl": [(900, 1100), (1130, 1230), (1300, 1430), (1500, 1600), (1630, 1700)]
}

# Angela's preference to avoid meetings before 15:00
angela_avoid_before = 1500

# Create a Z3 solver instance
solver = Solver()

# Define a variable for the start time of the meeting
start_time = Int('start_time')

# Define the constraints
# The meeting must start and end within the work hours
solver.add(start_time >= 900)
solver.add(start_time + 30 <= 1700)

# The meeting should not overlap with any busy times
for participant, busy_times in participants.items():
    for start, end in busy_times:
        solver.add(Or(start_time + 30 <= start, start_time >= end))

# Angela's preference to avoid meetings before 15:00
solver.add(start_time >= angela_avoid_before)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    start = model[start_time].as_long()
    end = start + 30
    print("SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {start // 100:02}:{start % 100:02}")
    print(f"End Time: {end // 100:02}:{end % 100:02}")
else:
    print("No solution found")