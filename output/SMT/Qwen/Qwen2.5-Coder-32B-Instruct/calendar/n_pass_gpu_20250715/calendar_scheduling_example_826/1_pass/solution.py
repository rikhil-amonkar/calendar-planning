from z3 import *

# Define the variables for the day and time
day = Int('day')
start_hour = Int('start_hour')
start_minute = Int('start_minute')

# Define the days of the week as integers (Monday=0, Tuesday=1, Wednesday=2, Thursday=3)
monday, tuesday, wednesday, thursday = 0, 1, 2, 3

# Constraints for the day
day_constraints = [
    Or(day == monday, day == tuesday, day == wednesday, day == thursday)
]

# Constraints for the time (9:00 to 17:00, 30-minute slots)
time_constraints = [
    And(start_hour >= 9, start_hour <= 16),  # Start hour between 9 and 16
    Or(start_minute == 0, start_minute == 30)  # Start minute either 0 or 30
]

# Cheryl's calendar is wide open, so no additional constraints for her

# James' busy times
james_busy_times = [
    (monday, 9, 9, 30),
    (monday, 10, 30, 11, 0),
    (monday, 12, 30, 13, 0),
    (monday, 14, 30, 15, 30),
    (monday, 16, 30, 17, 0),
    (tuesday, 9, 9, 11, 0),
    (tuesday, 11, 30, 12, 0),
    (tuesday, 12, 30, 15, 30),
    (tuesday, 16, 0, 17, 0),
    (wednesday, 10, 10, 11, 0),
    (wednesday, 12, 12, 13, 0),
    (wednesday, 13, 30, 16, 0),
    (thursday, 9, 30, 11, 30),
    (thursday, 12, 0, 12, 30),
    (thursday, 13, 0, 13, 30),
    (thursday, 14, 0, 14, 30),
    (thursday, 16, 30, 17, 0)
]

# Constraint to ensure the meeting does not overlap with James' busy times
james_availability_constraints = []
for d, sh, sm, eh, em in james_busy_times:
    # Meeting from start_time to start_time + 30 minutes should not overlap with James' busy times
    james_availability_constraints.append(
        Not(And(day == d, Or(
            And(start_hour == sh, start_minute >= sm),
            And(start_hour > sh, start_hour < eh),
            And(start_hour == eh, start_minute < em)
        )))
    )

# Preference: Cheryl would rather not meet on Wednesday or Thursday
preference_constraints = [
    Or(day == monday, day == tuesday)
]

# Create the solver
solver = Solver()

# Add all constraints to the solver
solver.add(day_constraints)
solver.add(time_constraints)
solver.add(james_availability_constraints)
solver.add(preference_constraints)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    meeting_day = ["Monday", "Tuesday", "Wednesday", "Thursday"][model[day].as_long()]
    meeting_start_hour = model[start_hour].as_long()
    meeting_start_minute = model[start_minute].as_long()
    meeting_end_hour = meeting_start_hour + (meeting_start_minute + 30) // 60
    meeting_end_minute = (meeting_start_minute + 30) % 60
    
    print(f"SOLUTION:\nDay: {meeting_day}\nStart Time: {meeting_start_hour:02}:{meeting_start_minute:02}\nEnd Time: {meeting_end_hour:02}:{meeting_end_minute:02}")
else:
    print("No solution found")