from z3 import *

# Define the variables
day = String('day')
start_time = Int('start_time')
end_time = Int('end_time')

# Define the constraints
constraints = []

# Define the meeting duration
meeting_duration = 30

# Define the available time slots for each person
available_slots = {
    'Gregory': [(930, 1130), (1200, 1700)],
    'Jonathan': [(900, 900), (930, 1200), (1230, 1300), (1330, 1500), (1600, 1630)],
    'Barbara': [(900, 1000), (1030, 1330), (1400, 1700)],
    'Jesse': [(900, 1000), (1100, 1230), (1430, 1700)],
    'Alan': [(900, 930), (1100, 1130), (1230, 1300), (1530, 1600)],
    'Nicole': [(900, 900), (1030, 1130), (1200, 1230), (1330, 1400)],
    'Catherine': [(900, 900), (1030, 1200), (1330, 1500), (1530, 1600), (1630, 1630)]
}

# Convert times to minutes since 9:00 AM for easier comparison
def convert_to_minutes(time):
    return (time // 100 - 9) * 60 + time % 100

# Add constraints for each person
for person, slots in available_slots.items():
    # Convert slots to minutes
    slots_in_minutes = [(convert_to_minutes(start), convert_to_minutes(end)) for start, end in slots]
    # Create a constraint that the meeting must fit into one of these slots
    person_constraints = Or([And(start_time >= convert_to_minutes(start), end_time <= convert_to_minutes(end))
                            for start, end in slots_in_minutes])
    constraints.append(person_constraints)

# The meeting duration constraint
constraints.append(end_time == start_time + meeting_duration)

# The meeting must be within working hours (9:00 AM to 5:00 PM)
constraints.append(start_time >= 0)
constraints.append(end_time <= 480)  # 480 minutes is 8 hours, which is 5:00 PM

# Create the solver and add the constraints
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    start_hour = (model[start_time].as_long() // 60) + 9
    start_minute = model[start_time].as_long() % 60
    end_hour = (model[end_time].as_long() // 60) + 9
    end_minute = model[end_time].as_long() % 60
    print(f"SOLUTION:\nDay: Monday\nStart Time: {start_hour:02}:{start_minute:02}\nEnd Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found")