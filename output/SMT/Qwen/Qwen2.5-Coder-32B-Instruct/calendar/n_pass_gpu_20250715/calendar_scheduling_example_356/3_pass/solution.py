from z3 import *

# Define the time slots from 9:00 to 17:00 in 30-minute increments
time_slots = [(h, m) for h in range(9, 17) for m in [0, 30]]

# Create a variable for the start time of the meeting
start_hour = Int('start_hour')
start_minute = Int('start_minute')

# Constraints for the start time
constraints = [
    start_hour >= 9,
    start_hour <= 16,
    Or(start_minute == 0, start_minute == 30)
]

# Function to check if a person is free at a given time slot
def is_free(person_schedule, hour, minute):
    return Not(Or([And(hour == s[0], minute == s[1]) for s in person_schedule]))

# Define the busy times for each person
katherine_busy = [(12, 0), (12, 30), (13, 0), (13, 30), (14, 0), (14, 30)]
rebecca_busy = []
julie_busy = [(9, 0), (9, 30), (10, 30), (11, 0), (13, 30), (14, 0), (15, 0), (15, 30)]
angela_busy = [(9, 0), (9, 30), (10, 30), (11, 0), (11, 30), (12, 0), (12, 30), (13, 0), (13, 30), (14, 0), (14, 30), (15, 0), (15, 30), (16, 30), (17, 0)]
nicholas_busy = [(9, 30), (10, 0), (10, 30), (11, 0), (11, 30), (12, 0), (12, 30), (13, 0), (13, 30), (14, 0), (14, 30), (15, 0), (15, 30), (16, 0), (16, 30), (17, 0)]
carl_busy = [(9, 0), (9, 30), (10, 0), (10, 30), (11, 0), (11, 30), (12, 0), (12, 30), (13, 0), (13, 30), (14, 0), (14, 30), (15, 0), (15, 30), (16, 0), (16, 30), (17, 0)]

# Add constraints for each person to be free at the start time
constraints.append(is_free(katherine_busy, start_hour, start_minute))
constraints.append(is_free(rebecca_busy, start_hour, start_minute))
constraints.append(is_free(julie_busy, start_hour, start_minute))
constraints.append(is_free(angela_busy, start_hour, start_minute))
constraints.append(is_free(nicholas_busy, start_hour, start_minute))
constraints.append(is_free(carl_busy, start_hour, start_minute))

# Angela's preference to avoid meetings before 15:00
constraints.append(Or(start_hour > 14, And(start_hour == 14, start_minute == 30)))

# Create the solver and add constraints
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    start_h = model[start_hour].as_long()
    start_m = model[start_minute].as_long()
    end_h = start_h + (start_m + 30) // 60
    end_m = (start_m + 30) % 60
    print(f"SOLUTION:\nDay: Monday\nStart Time: {start_h:02}:{start_m:02}\nEnd Time: {end_h:02}:{end_m:02}")
else:
    print("No solution found")