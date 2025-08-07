from z3 import *

# Define the time slots in 30-minute increments from 9:00 to 17:00
time_slots = [900, 930, 1000, 1030, 1100, 1130, 1200, 1230, 1300, 1330, 1400, 1430, 1500, 1530, 1600, 1630]

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
# The meeting must start at a valid time slot
solver.add(Or([start_time == t for t in time_slots]))

# The meeting must end at a valid time slot (30 minutes after the start time)
end_time = start_time + 30

# The meeting must end before 17:00
solver.add(end_time <= 1700)

# The meeting must not overlap with any busy times of the participants
for participant in participants:
    for busy_start, busy_end in busy_times[participant]:
        # The meeting must not start before the busy period ends and must not end after the busy period starts
        solver.add(Or(start_time >= busy_end, end_time <= busy_start))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    start_time_value = model[start_time].as_long()
    end_time_value = start_time_value + 30
    start_time_str = f"{start_time_value // 100:02}:{start_time_value % 100:02}"
    end_time_str = f"{end_time_value // 100:02}:{end_time_value % 100:02}"
    print(f"SOLUTION:\nDay: Monday\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
else:
    print("No solution found")