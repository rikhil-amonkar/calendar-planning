from z3 import *

# Define the time slots in 30-minute increments from 9:00 to 17:00
time_slots = [900, 930, 1000, 1030, 1100, 1130, 1200, 1230, 1300, 1330, 1400, 1430, 1500, 1530, 1600, 1630, 1700]

# Define the participants
participants = ["Joan", "Megan", "Austin", "Betty", "Judith", "Terry", "Kathryn"]

# Define the busy times for each participant
busy_times = {
    "Joan": [(1130, 1200), (1430, 1500)],
    "Megan": [(900, 1000), (1400, 1430), (1600, 1630)],
    "Austin": [],
    "Betty": [(930, 1000), (1130, 1200), (1330, 1400), (1600, 1630)],
    "Judith": [(900, 1100), (1200, 1300), (1400, 1500)],
    "Terry": [(930, 1000), (1130, 1230), (1300, 1400), (1500, 1530), (1600, 1700)],
    "Kathryn": [(930, 1000), (1030, 1100), (1130, 1300), (1400, 1600), (1630, 1700)]
}

# Create a Z3 solver
solver = Solver()

# Define a variable for the start time of the meeting
start_time = Int('start_time')

# Define the constraints
# The meeting must start and end within the work hours (9:00 to 17:00)
solver.add(start_time >= 900)
solver.add(start_time <= 1630)  # 16:30 is the latest start time for a 30-minute meeting to end by 17:00

# The meeting must not overlap with any busy times
for participant in participants:
    for busy_start, busy_end in busy_times[participant]:
        # The meeting should not start during a busy time
        solver.add(Or(start_time < busy_start, start_time >= busy_end))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    start = model[start_time].as_long()
    end = start + 30  # Meeting duration is 30 minutes
    print("SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {start // 100:02}:{start % 100:02}")
    print(f"End Time: {end // 100:02}:{end % 100:02}")
else:
    print("No solution found")