from z3 import *

# Define the time slots in 30-minute increments from 9:00 to 17:00
time_slots = [900, 930, 1000, 1030, 1100, 1130, 1200, 1230, 1300, 1330, 1400, 1430, 1500, 1530, 1600, 1630]

# Define the participants
participants = ["Judy", "Olivia", "Eric", "Jacqueline", "Laura", "Tyler", "Lisa"]

# Define the blocked time slots for each participant
blocked_slots = {
    "Judy": [1300, 1330, 1600, 1630],
    "Olivia": [1000, 1030, 1200, 1300, 1400, 1430],
    "Eric": [],
    "Jacqueline": [1000, 1030, 1500, 1530],
    "Laura": [900, 1000, 1030, 1200, 1300, 1330, 1430, 1500, 1530, 1700],
    "Tyler": [900, 1000, 1100, 1130, 1230, 1300, 1400, 1430, 1530, 1700],
    "Lisa": [930, 1030, 1100, 1130, 1200, 1230, 1300, 1330, 1400, 1430, 1600, 1700]
}

# Create a Z3 solver
solver = Solver()

# Define a boolean variable for each time slot indicating if the meeting can start at that time
meeting_start = {t: Bool(f"meeting_start_{t}") for t in time_slots}

# Add constraints that the meeting can only start at a time slot that is not blocked by any participant
for t in time_slots:
    if t + 30 in time_slots:  # Ensure there is a valid end time
        for participant in participants:
            if t in blocked_slots[participant] or t + 30 in blocked_slots[participant]:
                solver.add(Not(meeting_start[t]))

# Add constraints that only one time slot can be the start of the meeting
solver.add(Or([meeting_start[t] for t in time_slots]))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    for t in time_slots:
        if model.evaluate(meeting_start[t]):
            start_time = t
            end_time = t + 30
            break

    # Format the output
    start_time_str = f"{start_time // 100:02}:{start_time % 100:02}"
    end_hour = end_time // 100
    end_minute = end_time % 100
    if end_minute == 60:
        end_hour += 1
        end_minute = 0
    end_time_str = f"{end_hour:02}:{end_minute:02}"
    print(f"SOLUTION:\nDay: Monday\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
else:
    print("No solution found")