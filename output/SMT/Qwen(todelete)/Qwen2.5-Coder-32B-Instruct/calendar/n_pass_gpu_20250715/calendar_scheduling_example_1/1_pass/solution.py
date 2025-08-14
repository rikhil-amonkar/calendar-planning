from z3 import *

# Define the time slots as integers from 0 to 48 representing 30-minute intervals from 9:00 to 17:00
time_slots = range(49)  # 9:00 to 16:30 (inclusive)

# Create a variable to represent the start time of the meeting
start_time = Int('start_time')

# Define the constraints for each participant
raymond_unavailable = [0, 1, 9, 10, 16, 17, 24, 25]  # 9:00-9:30, 11:30-12:00, 13:00-13:30, 15:00-15:30
billy_unavailable = [2, 3, 8, 9, 10, 11, 27, 28, 29, 30]  # 10:00-10:30, 12:00-13:00, 16:30-17:00
donald_unavailable = [0, 1, 2, 3, 8, 9, 10, 11, 16, 17, 20, 21, 32, 33, 34, 35]  # 9:00-9:30, 10:00-11:00, 12:00-13:00, 14:00-14:30, 16:00-17:00

# Billy prefers not to have meetings after 15:00, which corresponds to time slots 30 and above
billy_preference = [i for i in range(30, 49)]

# Define the solver
solver = Solver()

# Add constraints that the meeting must fit within working hours and last for 30 minutes
solver.add(start_time >= 0)
solver.add(start_time <= 47)  # The latest start time is 16:30 (slot 47), so the meeting can end at 17:00 (slot 48)

# Add constraints that the meeting does not overlap with any unavailable times
for t in raymond_unavailable:
    solver.add(start_time != t)
    solver.add(start_time + 1 != t)

for t in billy_unavailable:
    solver.add(start_time != t)
    solver.add(start_time + 1 != t)

for t in donald_unavailable:
    solver.add(start_time != t)
    solver.add(start_time + 1 != t)

# Add Billy's preference constraint
for t in billy_preference:
    solver.add(start_time != t)
    solver.add(start_time + 1 != t)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    start_slot = model[start_time].as_long()
    start_time_str = f"{9 + start_slot // 2}:{'00' if start_slot % 2 == 0 else '30'}"
    end_time_str = f"{9 + (start_slot + 1) // 2}:{'00' if (start_slot + 1) % 2 == 0 else '30'}"
    print(f"SOLUTION:\nDay: Monday\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
else:
    print("No solution found")