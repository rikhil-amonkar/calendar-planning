from z3 import *

# Define the time slots in 30-minute increments from 9:00 to 17:00
time_slots = [900, 930, 1000, 1030, 1100, 1130, 1200, 1230, 1300, 1330, 1400, 1430, 1500, 1530, 1600, 1630]

# Define the participants and their blocked time slots
participants = {
    "Doris": [900, 930, 1000, 1030, 1330, 1400, 1600, 1630],
    "Theresa": [1000, 1030, 1100, 1130],
    "Christian": [],
    "Terry": [930, 1000, 1030, 1130, 1200, 1230, 1330, 1400, 1430, 1500, 1530, 1600, 1630],
    "Carolyn": [900, 930, 1000, 1030, 1100, 1130, 1200, 1230, 1330, 1400, 1430, 1500, 1530, 1600, 1630],
    "Kyle": [900, 930, 1130, 1200, 1230, 1430, 1500, 1530, 1600, 1630]
}

# Create a Z3 solver
solver = Solver()

# Define a boolean variable for each time slot indicating if the meeting can start at that time
meeting_start = [Bool(f"meeting_start_{t}") for t in time_slots]

# Add constraints to ensure the meeting can only start at a time slot that is not blocked by any participant
for t in time_slots:
    for participant, blocked_slots in participants.items():
        if t in blocked_slots or (t + 30) in blocked_slots:
            solver.add(Not(meeting_start[time_slots.index(t)]))

# Add constraints to ensure the meeting duration of 30 minutes fits within the workday
for i in range(len(time_slots) - 1):
    solver.add(Implies(meeting_start[i], Not(meeting_start[i + 1])))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    start_time = None
    for i, t in enumerate(time_slots):
        if model.evaluate(meeting_start[i]):
            start_time = t
            end_time = t + 30
            break

    if start_time is not None:
        # Format the output
        start_time_str = f"{start_time // 100:02}:{start_time % 100:02}"
        end_time_str = f"{end_time // 100:02}:{end_time % 100:02}"
        print(f"SOLUTION:\nDay: Monday\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
    else:
        print("No valid meeting time found despite a satisfiable model.")
else:
    print("No solution found")