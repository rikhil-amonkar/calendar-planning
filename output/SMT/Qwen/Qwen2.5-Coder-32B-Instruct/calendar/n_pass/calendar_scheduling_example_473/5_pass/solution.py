from z3 import *

# Define the variables
start_time = Int('start_time')
end_time = Int('end_time')

# Define the meeting duration
meeting_duration = 30

# Define the available time slots for each person in minutes since 9:00 AM
available_slots = {
    'Gregory': [(9*60 + 0, 9*60 + 30), (11*60 + 30, 12*60 + 0), (12*60 + 0, 17*60 + 0)],
    'Jonathan': [(9*60 + 0, 9*60 + 30), (12*60 + 0, 12*60 + 30), (13*60 + 0, 13*60 + 30), (15*60 + 0, 16*60 + 0), (16*60 + 30, 17*60 + 0)],
    'Barbara': [(10*60 + 0, 10*60 + 30), (13*60 + 30, 14*60 + 0), (14*60 + 0, 17*60 + 0)],
    'Jesse': [(10*60 + 0, 11*60 + 0), (12*60 + 30, 14*60 + 30), (14*60 + 30, 17*60 + 0)],
    'Alan': [(9*60 + 30, 11*60 + 0), (11*60 + 30, 12*60 + 30), (13*60 + 0, 15*60 + 30), (16*60 + 0, 17*60 + 0)],
    'Nicole': [(9*60 + 0, 10*60 + 30), (11*60 + 30, 12*60 + 0), (12*60 + 30, 13*60 + 30), (14*60 + 0, 17*60 + 0)],
    'Catherine': [(9*60 + 0, 10*60 + 30), (12*60 + 0, 13*60 + 30), (15*60 + 0, 15*60 + 30), (16*60 + 0, 16*60 + 30), (16*60 + 30, 17*60 + 0)]
}

# Create the solver
solver = Solver()

# Add constraints for each person
for person, slots in available_slots.items():
    person_constraints = Or([And(start_time >= start, end_time <= end) for start, end in slots])
    solver.add(person_constraints)

# The meeting duration constraint
solver.add(end_time == start_time + meeting_duration)

# The meeting must be within working hours (9:00 AM to 5:00 PM)
solver.add(start_time >= 0)
solver.add(end_time <= 480)  # 480 minutes is 8 hours, which is 5:00 PM

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