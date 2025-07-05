from z3 import *

# Define the time slots in 30-minute increments from 9:00 to 17:00
time_slots = [(h, m) for h in range(9, 17) for m in [0, 30]]

# Create a boolean variable for each time slot indicating if the meeting can start then
meeting_start = BoolVector('meeting_start', len(time_slots))

# Helper function to convert time slot index to string representation
def time_slot_to_string(slot_index):
    h, m = time_slots[slot_index]
    return f"{h:02}:{m:02}"

# Define the constraints for each participant
constraints = []

# Joe's constraints
joe_unavailable = [(9, 30), (10, 0), (10, 30), (11, 0)]
constraints.extend([Not(meeting_start[time_slots.index(t)]) for t in joe_unavailable])

# Keith's constraints
keith_unavailable = [(11, 30), (15, 0)]
constraints.extend([Not(meeting_start[time_slots.index(t)]) for t in keith_unavailable])

# Patricia's constraints
patricia_unavailable = [(9, 0), (13, 0)]
constraints.extend([Not(meeting_start[time_slots.index(t)]) for t in patricia_unavailable])

# Nancy's constraints
nancy_unavailable = [(9, 0), (10, 0), (11, 30), (12, 0), (13, 0), (14, 0), (15, 0), (16, 0)]
constraints.extend([Not(meeting_start[time_slots.index(t)]) for t in nancy_unavailable])

# Pamela's constraints
pamela_unavailable = [(9, 0), (10, 0), (10, 30), (11, 30), (13, 0), (14, 0), (14, 30), (15, 0), (15, 30), (16, 0), (16, 30)]
constraints.extend([Not(meeting_start[time_slots.index(t)]) for t in pamela_unavailable])

# Ensure that the meeting time is exactly 30 minutes long
for i in range(len(time_slots) - 1):
    constraints.append(Implies(meeting_start[i], Not(meeting_start[i + 1])))

# Ensure that there is exactly one valid start time for the meeting
constraints.append(Or(meeting_start))

# Add the constraints to the solver
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    # Find the first time slot that is True in the model
    for i in range(len(time_slots)):
        if model.evaluate(meeting_start[i]):
            start_time = time_slot_to_string(i)
            end_time = time_slot_to_string(i + 1)
            print(f"SOLUTION:\nDay: Monday\nStart Time: {start_time}\nEnd Time: {end_time}")
            break
else:
    print("No solution found")