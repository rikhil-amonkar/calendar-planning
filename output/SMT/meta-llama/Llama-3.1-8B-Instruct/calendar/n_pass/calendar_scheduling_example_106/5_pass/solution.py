from z3 import *

# Define the time slots
time_slots = [
    "09:00", "09:30", "10:00", "10:30", "11:00", "11:30", "12:00", "12:30",
    "13:00", "13:30", "14:00", "14:30", "15:00", "15:30", "16:00", "16:30",
    "17:00"
]

# Convert time slots to minutes
time_slots_minutes = [int(time_slot[:2]) * 60 + int(time_slot[3:]) for time_slot in time_slots]

# Define the existing schedules
schedules = {
    "Olivia": [time_slots_minutes[6], time_slots_minutes[7], time_slots_minutes[9], time_slots_minutes[15]],
    "Anna": [],
    "Virginia": [time_slots_minutes[0], time_slots_minutes[5], time_slots_minutes[10], time_slots_minutes[15]],
    "Paul": [time_slots_minutes[0], time_slots_minutes[3], time_slots_minutes[6], time_slots_minutes[9], time_slots_minutes[10], time_slots_minutes[15]]
}

# Define the meeting duration
meeting_duration = 60

# Define the solver
solver = Solver()

# Define the variables
day = "Monday"
start_time = Int("start_time")

# Add constraints for each participant
for participant in schedules:
    for time in schedules[participant]:
        solver.add(start_time + meeting_duration > time)

# Add constraints for the day
solver.add(start_time >= time_slots_minutes[0])
solver.add(start_time + meeting_duration <= time_slots_minutes[-1])

# Add constraints for the meeting duration
solver.add(start_time % 60 == 0)

# Check if a solution exists
if solver.check() == sat:
    # Get the solution
    model = solver.model()
    start_time_value = model[start_time].as_long()

    # Find a valid end time
    for i in range(time_slots_minutes[-1] - 59):
        if i // 60 == start_time_value // 60:
            end_time_value = i + 60
            break

    # Convert the start and end times back to the original format
    start_time_str = time_slots[start_time_value // 60] + ":" + str(start_time_value % 60).zfill(2)
    end_time_str = time_slots[end_time_value // 60] + ":" + str(end_time_value % 60).zfill(2)

    # Print the solution
    print("SOLUTION:")
    print(f"Day: {day}")
    print(f"Start Time: {start_time_str}")
    print(f"End Time: {end_time_str}")
else:
    print("No solution exists.")