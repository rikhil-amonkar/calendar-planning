from z3 import *

# Define the time slots in 30-minute increments from 9:00 to 17:00
time_slots = [(h, m) for h in range(9, 17) for m in [0, 30]]

# Convert time slots to minutes since 9:00 for easier comparison
time_to_minutes = {(h, m): (h - 9) * 60 + m for h, m in time_slots}

# Create a boolean variable for each time slot indicating if the meeting starts then
meeting_starts = {ts: Bool(f"meeting_start_{ts[0]}_{ts[1]}") for ts in time_slots}

# Define the constraints for each participant
def add_constraints_for_participant(solver, person_schedule):
    for start_h, start_m in person_schedule:
        start_minutes = time_to_minutes[(start_h, start_m)]
        end_minutes = start_minutes + 30  # Meetings are 30 minutes long
        for h, m in time_slots:
            current_minutes = time_to_minutes[(h, m)]
            if start_minutes <= current_minutes < end_minutes:
                solver.add(Not(meeting_starts[(h, m)]))

# Create the solver instance
solver = Solver()

# Add constraints for each participant
add_constraints_for_participant(solver, [(9, 0), (10, 30), (11, 30), (13, 0), (15, 0)])  # Margaret
add_constraints_for_participant(solver, [(14, 30), (16, 0)])  # Donna
add_constraints_for_participant(solver, [(9, 0), (10, 0), (13, 0), (14, 30), (15, 30)])  # Helen

# Add the constraint that Helen does not want to meet after 13:30
for h, m in time_slots:
    if h > 13 or (h == 13 and m > 30):
        solver.add(Not(meeting_starts[(h, m)]))

# Ensure that exactly one meeting_start is True
solver.add(Or([meeting_starts[ts] for ts in time_slots]))
solver.add(Not(And([meeting_starts[ts] for ts in time_slots])))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    for ts in time_slots:
        if is_true(model[meeting_starts[ts]]):
            day = "Monday"
            start_time = f"{ts[0]:02}:{ts[1]:02}"
            end_time = f"{ts[0] + (ts[1] + 30) // 60:02}:{(ts[1] + 30) % 60:02}"
            print(f"SOLUTION:\nDay: {day}\nStart Time: {start_time}\nEnd Time: {end_time}")
            break
else:
    print("No solution found")