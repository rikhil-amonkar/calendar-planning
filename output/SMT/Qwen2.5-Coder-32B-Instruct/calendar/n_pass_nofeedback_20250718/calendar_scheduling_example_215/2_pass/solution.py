from z3 import *

# Define the time slots in 30-minute increments from 9:00 to 17:00
time_slots = [(h, m) for h in range(9, 17) for m in [0, 30]]

# Create a Z3 solver instance
solver = Solver()

# Define boolean variables for each person's availability at each time slot
availability = {}
for person in ["Steven", "Roy", "Cynthia", "Lauren", "Robert"]:
    availability[person] = [Bool(f"{person}_{h:02d}{m:02d}") for h, m in time_slots]

# Define the constraints for each person's availability
# Steven and Roy are free the entire day
for h, m in time_slots:
    solver.add(availability["Steven"][time_slots.index((h, m))])
    solver.add(availability["Roy"][time_slots.index((h, m))])

# Cynthia's busy times: 9:30-10:30, 11:30-12:00, 13:00-13:30, 15:00-16:00
busy_times_cynthia = [(9, 30), (10, 0), (10, 30), (11, 30), (12, 0), (13, 0), (13, 30), (15, 0), (15, 30), (16, 0)]
for h, m in time_slots:
    if (h, m) in busy_times_cynthia or (h, m - 30) in busy_times_cynthia:
        solver.add(Not(availability["Cynthia"][time_slots.index((h, m))]))

# Lauren's busy times: 9:00-9:30, 10:30-11:00, 11:30-12:00, 13:00-13:30, 14:00-14:30, 15:00-15:30, 16:00-17:00
busy_times_lauren = [(9, 0), (9, 30), (10, 30), (11, 0), (11, 30), (12, 0), (13, 0), (13, 30), (14, 0), (14, 30), (15, 0), (15, 30), (16, 0)]
for h, m in time_slots:
    if (h, m) in busy_times_lauren or (h, m - 30) in busy_times_lauren:
        solver.add(Not(availability["Lauren"][time_slots.index((h, m))]))

# Robert's busy times: 10:30-11:00, 11:30-12:00, 12:30-13:30, 14:00-16:00
busy_times_robert = [(10, 30), (11, 0), (11, 30), (12, 0), (12, 30), (13, 0), (13, 30), (14, 0), (14, 30), (15, 0), (15, 30), (16, 0)]
for h, m in time_slots:
    if (h, m) in busy_times_robert or (h, m - 30) in busy_times_robert:
        solver.add(Not(availability["Robert"][time_slots.index((h, m))]))

# Define the meeting duration (30 minutes)
meeting_duration = 1

# Add constraints to find a 30-minute slot where all are available
for i in range(len(time_slots) - meeting_duration + 1):
    meeting_slot = [availability[person][i] for person in ["Steven", "Roy", "Cynthia", "Lauren", "Robert"]]
    solver.add(Or(Not(And(meeting_slot)), And([availability[person][i + j] for person in ["Steven", "Roy", "Cynthia", "Lauren", "Robert"] for j in range(meeting_duration)])))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    for i in range(len(time_slots) - meeting_duration + 1):
        meeting_slot = [model.evaluate(availability[person][i]) for person in ["Steven", "Roy", "Cynthia", "Lauren", "Robert"]]
        if all([is_true(slot) for slot in meeting_slot]):
            start_hour, start_minute = time_slots[i]
            end_hour, end_minute = time_slots[i + meeting_duration - 1]
            if end_minute == 30:
                end_hour += 1
                end_minute = 0
            print("SOLUTION:")
            print(f"Day: Monday")
            print(f"Start Time: {start_hour:02d}:{start_minute:02d}")
            print(f"End Time: {end_hour:02d}:{end_minute:02d}")
            break
else:
    print("No solution found")