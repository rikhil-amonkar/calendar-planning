from z3 import *

# Define the time slots from 9:00 to 16:30 in 30-minute intervals
time_slots = [(h, m) for h in range(9, 17) for m in [0, 30]]

# Create a dictionary to hold the availability of each person for each time slot
availability = {name: [Bool(f"{name}_{h:02d}{m:02d}") for h, m in time_slots] for name in ["Andrea", "Ruth", "Steven", "Grace", "Kyle", "Elijah", "Lori"]}

# Define the constraints based on the given schedules
constraints = []

# Andrea is busy on Monday during 9:30 to 10:30, 13:30 to 14:30
constraints.append(Not(availability["Andrea"][time_slots.index((9, 30))]))
constraints.append(Not(availability["Andrea"][time_slots.index((10, 0))]))
constraints.append(Not(availability["Andrea"][time_slots.index((13, 30))]))
constraints.append(Not(availability["Andrea"][time_slots.index((14, 0))]))

# Ruth has blocked their calendar on Monday during 12:30 to 13:00, 15:00 to 15:30
constraints.append(Not(availability["Ruth"][time_slots.index((12, 30))]))
constraints.append(Not(availability["Ruth"][time_slots.index((13, 0))]))
constraints.append(Not(availability["Ruth"][time_slots.index((15, 0))]))
constraints.append(Not(availability["Ruth"][time_slots.index((15, 30))]))

# Steven is busy on Monday during 10:00 to 10:30, 11:00 to 11:30, 12:00 to 12:30, 13:30 to 14:00, 15:00 to 16:00
constraints.append(Not(availability["Steven"][time_slots.index((10, 0))]))
constraints.append(Not(availability["Steven"][time_slots.index((10, 30))]))
constraints.append(Not(availability["Steven"][time_slots.index((11, 0))]))
constraints.append(Not(availability["Steven"][time_slots.index((11, 30))]))
constraints.append(Not(availability["Steven"][time_slots.index((12, 0))]))
constraints.append(Not(availability["Steven"][time_slots.index((12, 30))]))
constraints.append(Not(availability["Steven"][time_slots.index((13, 30))]))
constraints.append(Not(availability["Steven"][time_slots.index((14, 0))]))
constraints.append(Not(availability["Steven"][time_slots.index((15, 0))]))
constraints.append(Not(availability["Steven"][time_slots.index((15, 30))]))
constraints.append(Not(availability["Steven"][time_slots.index((16, 0))]))

# Grace has no meetings the whole day (all slots are available)

# Kyle is busy on Monday during 9:00 to 9:30, 10:30 to 12:00, 12:30 to 13:00, 13:30 to 15:00, 15:30 to 16:00, 16:30 to 17:00
constraints.append(Not(availability["Kyle"][time_slots.index((9, 0))]))
constraints.append(Not(availability["Kyle"][time_slots.index((9, 30))]))
constraints.append(Not(availability["Kyle"][time_slots.index((10, 30))]))
constraints.append(Not(availability["Kyle"][time_slots.index((11, 0))]))
constraints.append(Not(availability["Kyle"][time_slots.index((11, 30))]))
constraints.append(Not(availability["Kyle"][time_slots.index((12, 0))]))
constraints.append(Not(availability["Kyle"][time_slots.index((12, 30))]))
constraints.append(Not(availability["Kyle"][time_slots.index((13, 30))]))
constraints.append(Not(availability["Kyle"][time_slots.index((14, 0))]))
constraints.append(Not(availability["Kyle"][time_slots.index((14, 30))]))
constraints.append(Not(availability["Kyle"][time_slots.index((15, 0))]))
constraints.append(Not(availability["Kyle"][time_slots.index((15, 30))]))
constraints.append(Not(availability["Kyle"][time_slots.index((16, 0))]))
constraints.append(Not(availability["Kyle"][time_slots.index((16, 30))]))

# Elijah has blocked their calendar on Monday during 9:00 to 11:00, 11:30 to 13:00, 13:30 to 14:00, 15:30 to 16:00, 16:30 to 17:00
constraints.append(Not(availability["Elijah"][time_slots.index((9, 0))]))
constraints.append(Not(availability["Elijah"][time_slots.index((9, 30))]))
constraints.append(Not(availability["Elijah"][time_slots.index((10, 0))]))
constraints.append(Not(availability["Elijah"][time_slots.index((10, 30))]))
constraints.append(Not(availability["Elijah"][time_slots.index((11, 30))]))
constraints.append(Not(availability["Elijah"][time_slots.index((12, 0))]))
constraints.append(Not(availability["Elijah"][time_slots.index((12, 30))]))
constraints.append(Not(availability["Elijah"][time_slots.index((13, 30))]))
constraints.append(Not(availability["Elijah"][time_slots.index((14, 0))]))
constraints.append(Not(availability["Elijah"][time_slots.index((15, 30))]))
constraints.append(Not(availability["Elijah"][time_slots.index((16, 0))]))
constraints.append(Not(availability["Elijah"][time_slots.index((16, 30))]))

# Lori is busy on Monday during 9:00 to 9:30, 10:00 to 11:30, 12:00 to 13:30, 14:00 to 16:00, 16:30 to 17:00
constraints.append(Not(availability["Lori"][time_slots.index((9, 0))]))
constraints.append(Not(availability["Lori"][time_slots.index((9, 30))]))
constraints.append(Not(availability["Lori"][time_slots.index((10, 0))]))
constraints.append(Not(availability["Lori"][time_slots.index((10, 30))]))
constraints.append(Not(availability["Lori"][time_slots.index((11, 0))]))
constraints.append(Not(availability["Lori"][time_slots.index((11, 30))]))
constraints.append(Not(availability["Lori"][time_slots.index((12, 0))]))
constraints.append(Not(availability["Lori"][time_slots.index((12, 30))]))
constraints.append(Not(availability["Lori"][time_slots.index((13, 0))]))
constraints.append(Not(availability["Lori"][time_slots.index((13, 30))]))
constraints.append(Not(availability["Lori"][time_slots.index((14, 0))]))
constraints.append(Not(availability["Lori"][time_slots.index((14, 30))]))
constraints.append(Not(availability["Lori"][time_slots.index((15, 0))]))
constraints.append(Not(availability["Lori"][time_slots.index((15, 30))]))
constraints.append(Not(availability["Lori"][time_slots.index((16, 0))]))
constraints.append(Not(availability["Lori"][time_slots.index((16, 30))]))

# Solve the constraints
s = Solver()
s.add(constraints)

# Check for a valid 30-minute slot where all participants are available
for i in range(len(time_slots) - 1):
    slot_available = And([availability[name][i] for name in availability])
    constraints.append(slot_available)

if s.check() == sat:
    model = s.model()
    for i in range(len(time_slots) - 1):
        if all(model.evaluate(availability[name][i]) for name in availability):
            start_time = f"{time_slots[i][0]:02d}:{time_slots[i][1]:02d}"
            end_time = f"{time_slots[i+1][0]:02d}:{time_slots[i+1][1]:02d}"
            print("SOLUTION:")
            print(f"Day: Monday")
            print(f"Start Time: {start_time}")
            print(f"End Time: {end_time}")
            break
else:
    print("No solution found.")