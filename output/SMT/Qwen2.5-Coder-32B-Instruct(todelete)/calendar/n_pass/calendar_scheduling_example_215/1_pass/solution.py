from z3 import *

# Define the time slots in 30-minute increments from 9:00 to 17:00
time_slots = [(h, m) for h in range(9, 17) for m in [0, 30]]

# Create a Z3 solver instance
solver = Solver()

# Define a boolean variable for each time slot indicating if the meeting can start at that time
meeting_start = {t: Bool(f"meeting_start_{t[0]}_{t[1]}") for t in time_slots}

# Define the duration of the meeting (30 minutes)
meeting_duration = 1

# Define the constraints for each participant
# Steven and Roy are free the entire day, so no constraints for them

# Cynthia's busy times: 9:30-10:30, 11:30-12:00, 13:00-13:30, 15:00-16:00
cynthia_busy_times = [(9, 30), (10, 0), (11, 30), (12, 0), (13, 0), (13, 30), (15, 0), (15, 30), (16, 0), (16, 30)]
for t in cynthia_busy_times:
    solver.add(Not(meeting_start[t]))

# Lauren's busy times: 9:00-9:30, 10:30-11:00, 11:30-12:00, 13:00-13:30, 14:00-14:30, 15:00-15:30, 16:00-17:00
lauren_busy_times = [(9, 0), (9, 30), (10, 30), (11, 0), (11, 30), (12, 0), (13, 0), (13, 30), (14, 0), (14, 30), (15, 0), (15, 30), (16, 0), (16, 30)]
for t in lauren_busy_times:
    solver.add(Not(meeting_start[t]))

# Robert's busy times: 10:30-11:00, 11:30-12:00, 12:30-13:30, 14:00-16:00
robert_busy_times = [(10, 30), (11, 0), (11, 30), (12, 0), (12, 30), (13, 0), (13, 30), (14, 0), (14, 30), (15, 0), (15, 30), (16, 0), (16, 30)]
for t in robert_busy_times:
    solver.add(Not(meeting_start[t]))

# Ensure that the meeting can only start at a time slot where all participants are free
for t in time_slots:
    if t[1] + 30 == 60:  # Handle the case where the meeting would end at the next hour
        next_hour = (t[0] + 1, 0)
        if next_hour in time_slots:
            solver.add(Implies(meeting_start[t], And(Not(meeting_start[(t[0], t[1] + 30)]), Not(meeting_start[next_hour]))))
    else:
        solver.add(Implies(meeting_start[t], Not(meeting_start[(t[0], t[1] + 30)])))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    for t in time_slots:
        if model.evaluate(meeting_start[t]):
            start_hour, start_minute = t
            end_hour, end_minute = (start_hour, start_minute + 30) if start_minute + 30 < 60 else (start_hour + 1, 0)
            print(f"SOLUTION:\nDay: Monday\nStart Time: {start_hour:02}:{start_minute:02}\nEnd Time: {end_hour:02}:{end_minute:02}")
            break
else:
    print("No solution found")