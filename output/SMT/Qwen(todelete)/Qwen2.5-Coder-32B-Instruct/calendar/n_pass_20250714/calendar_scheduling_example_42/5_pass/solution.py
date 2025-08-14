from z3 import *

# Define the time slots in 30-minute intervals from 9:00 to 16:30 (since meetings are 1 hour long)
time_slots = [(h, m) for h in range(9, 17) for m in [0, 30] if h != 16 or m != 30]

# Create a dictionary to map time slots to their index
time_index = {slot: i for i, slot in enumerate(time_slots)}

# Create a Z3 solver instance
solver = Solver()

# Define boolean variables for each person and each time slot
julie = [Bool(f"julie_{i}") for i in range(len(time_slots))]
sean = [Bool(f"sean_{i}") for i in range(len(time_slots))]
lori = [Bool(f"lori_{i}") for i in range(len(time_slots))]

# Define the constraints for Julie
blocked_julie = [(9, 0), (9, 30), (11, 0), (11, 30), (12, 0), (12, 30), (13, 30), (14, 0), (16, 0)]
for slot in blocked_julie:
    if slot in time_index:  # Ensure the slot is within our defined time slots
        solver.add(julie[time_index[slot]] == False)

# Define the constraints for Sean
blocked_sean = [(9, 0), (9, 30), (13, 0), (13, 30), (15, 0), (15, 30), (16, 0), (16, 30)]
for slot in blocked_sean:
    if slot in time_index:  # Ensure the slot is within our defined time slots
        solver.add(sean[time_index[slot]] == False)

# Define the constraints for Lori
blocked_lori = [(10, 0), (10, 30), (11, 0), (11, 30), (12, 0), (12, 30), (13, 0), (13, 30), (15, 30), (16, 0), (16, 30)]
for slot in blocked_lori:
    if slot in time_index:  # Ensure the slot is within our defined time slots
        solver.add(lori[time_index[slot]] == False)

# Ensure that the meeting time is available for all three
available_time = []
for i in range(len(time_slots) - 2):  # -2 because meeting is 1 hour
    start_slot = time_slots[i]
    end_slot = time_slots[i + 2]
    if end_slot not in blocked_julie and end_slot not in blocked_sean and end_slot not in blocked_lori:
        available_time.append(And(julie[i], sean[i], lori[i]))

# Add constraints to ensure there is exactly one valid meeting time
meeting_time = Or([available_time[i] for i in range(len(available_time))])
solver.add(meeting_time)

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    for i in range(len(available_time)):
        if model.evaluate(available_time[i]):
            start_hour, start_minute = time_slots[i]
            end_hour, end_minute = time_slots[i + 2]  # End time is 1 hour later
            print("SOLUTION:")
            print(f"Day: Monday")
            print(f"Start Time: {start_hour:02}:{start_minute:02}")
            print(f"End Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found")