from z3 import *

# Define the time slots from 9:00 to 17:00 in 30-minute intervals
time_slots = [(h, m) for h in range(9, 17) for m in [0, 30]]

# Create a boolean variable for each time slot indicating if the meeting can start at that time
meeting_start = BoolVector('meeting_start', len(time_slots))

# Define the constraints for each participant
constraints = []

# Megan's busy times: 9:00-9:30, 10:00-11:00, 12:00-12:30
megan_busy = [(9, 0), (9, 30), (10, 0), (10, 30), (12, 0), (12, 30)]
constraints.extend([Not(meeting_start[time_slots.index(t)]) for t in megan_busy])

# Christine's busy times: 9:00-9:30, 11:30-12:00, 13:00-14:00, 15:30-16:30
christine_busy = [(9, 0), (9, 30), (11, 30), (12, 0), (13, 0), (14, 0), (15, 30), (16, 0)]
constraints.extend([Not(meeting_start[time_slots.index(t)]) for t in christine_busy])

# Gabriel is free the entire day, so no constraints for him

# Sara's busy times: 11:30-12:00, 14:30-15:00
sara_busy = [(11, 30), (12, 0), (14, 30), (15, 0)]
constraints.extend([Not(meeting_start[time_slots.index(t)]) for t in sara_busy])

# Bruce's busy times: 9:30-10:00, 10:30-12:00, 12:30-14:00, 14:30-15:00, 15:30-16:30
bruce_busy = [(9, 30), (10, 0), (10, 30), (12, 0), (12, 30), (14, 0), (14, 30), (15, 0), (15, 30), (16, 0)]
constraints.extend([Not(meeting_start[time_slots.index(t)]) for t in bruce_busy])

# Kathryn's busy times: 10:00-15:30, 16:00-16:30
kathryn_busy = [(h, m) for h in range(10, 15) for m in [0, 30]] + [(15, 0), (15, 30), (16, 0)]
constraints.extend([Not(meeting_start[time_slots.index(t)]) for t in kathryn_busy])

# Billy's busy times: 9:00-9:30, 11:00-11:30, 12:00-14:00, 14:30-15:30
billy_busy = [(9, 0), (9, 30), (11, 0), (11, 30), (12, 0), (12, 30), (13, 0), (13, 30), (14, 0), (14, 30), (15, 0), (15, 30)]
constraints.extend([Not(meeting_start[time_slots.index(t)]) for t in billy_busy])

# Ensure that the meeting time is a continuous 30-minute slot
for i in range(len(meeting_start) - 1):
    constraints.append(Implies(meeting_start[i], Not(meeting_start[i+1])))

# Ensure that the meeting time does not overlap with busy times of other participants
for i in range(len(meeting_start) - 1):
    if (time_slots[i][1] == 0 and time_slots[i+1][1] == 30):
        constraints.append(Implies(meeting_start[i], And(
            Not(meeting_start[time_slots.index((time_slots[i][0], 30))]),
            Not(meeting_start[time_slots.index((time_slots[i+1][0], 0))])
        )))

# Create a solver instance and add the constraints
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    # Find the first time slot where the meeting can start
    for i in range(len(meeting_start)):
        if model.evaluate(meeting_start[i]):
            start_hour, start_minute = time_slots[i]
            end_hour, end_minute = time_slots[i+1] if i+1 < len(time_slots) else (start_hour + 1, 0)
            print("SOLUTION:")
            print(f"Day: Monday")
            print(f"Start Time: {start_hour:02}:{start_minute:02}")
            print(f"End Time: {end_hour:02}:{end_minute:02}")
            break
else:
    print("No solution found")