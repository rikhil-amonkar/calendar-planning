from z3 import *

# Define the time slots in 30-minute increments from 9:00 to 17:00
time_slots = [900, 930, 1000, 1030, 1100, 1130, 1200, 1230, 1300, 1330, 1400, 1430, 1500, 1530, 1600, 1630]

# Define the participants and their busy times
participants = {
    "Andrea": [],
    "Jack": [900, 930, 1400, 1430],
    "Madison": [930, 1030, 1300, 1400, 1500, 1530, 1630],
    "Rachel": [930, 1030, 1100, 1130, 1200, 1330, 1430, 1500, 1530, 1600],
    "Douglas": [900, 930, 1000, 1030, 1100, 1130, 1200, 1230, 1300, 1330, 1400, 1430, 1500, 1530, 1600, 1630],
    "Ryan": [900, 930, 1300, 1400, 1430, 1500, 1530, 1600]
}

# Create a Z3 solver instance
solver = Solver()

# Define a boolean variable for each time slot indicating if the meeting can start at that time
meeting_start_times = {time: Bool(f"meeting_start_{time}") for time in time_slots}

# Add constraints to the solver
# The meeting must start at one of the time slots
solver.add(Or([meeting_start_times[time] for time in time_slots]))

# The meeting must not start during a busy time for any participant
for participant, busy_times in participants.items():
    for time in time_slots:
        if time in busy_times or (time + 30) in busy_times:
            solver.add(Not(meeting_start_times[time]))

# The meeting must end before 17:00
for time in time_slots:
    if time + 30 > 1700:
        solver.add(Not(meeting_start_times[time]))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    for time in time_slots:
        if model.evaluate(meeting_start_times[time]):
            start_time = time
            end_time = time + 30
            start_time_str = f"{start_time // 100:02}:{start_time % 100:02}"
            end_time_str = f"{end_time // 100:02}:{end_time % 100:02}"
            print(f"SOLUTION:\nDay: Monday\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
            break
else:
    print("No solution found")