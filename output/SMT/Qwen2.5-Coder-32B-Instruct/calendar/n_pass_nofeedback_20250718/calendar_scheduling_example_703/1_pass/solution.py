from z3 import *

# Define the variables
day = Int('day')  # 0 = Monday, 1 = Tuesday, 2 = Wednesday
start_time = Int('start_time')  # in minutes from 00:00

# Define the constraints
solver = Solver()

# Work hours are from 9:00 to 17:00 (540 to 1020 minutes from 00:00)
solver.add(start_time >= 540)
solver.add(start_time + 60 <= 1020)  # Meeting duration is 1 hour

# Days are Monday, Tuesday, Wednesday (0, 1, 2)
solver.add(day >= 0)
solver.add(day <= 2)

# Stephanie's schedule
# Monday: 9:30-10:00, 10:30-11:00, 11:30-12:00, 14:00-14:30
solver.add(Or(day != 0, Or(start_time < 570, start_time >= 600)))
solver.add(Or(day != 0, Or(start_time < 630, start_time >= 660)))
solver.add(Or(day != 0, Or(start_time < 690, start_time >= 720)))
solver.add(Or(day != 0, Or(start_time < 840, start_time >= 870)))

# Tuesday: 12:00-13:00
solver.add(Or(day != 1, Or(start_time < 720, start_time >= 780)))

# Wednesday: 9:00-10:00, 13:00-14:00
solver.add(Or(day != 2, Or(start_time < 540, start_time >= 600)))
solver.add(Or(day != 2, Or(start_time < 780, start_time >= 840)))

# Betty's schedule
# Monday: 9:00-10:00, 11:00-11:30, 14:30-15:00, 15:30-16:00
solver.add(Or(day != 0, Or(start_time < 540, start_time >= 600)))
solver.add(Or(day != 0, Or(start_time < 660, start_time >= 690)))
solver.add(Or(day != 0, Or(start_time < 870, start_time >= 900)))
solver.add(Or(day != 0, Or(start_time < 930, start_time >= 960)))

# Tuesday: 9:00-9:30, 11:30-12:00, 12:30-14:30, 15:30-16:00
solver.add(Or(day != 1, Or(start_time < 540, start_time >= 570)))
solver.add(Or(day != 1, Or(start_time < 690, start_time >= 720)))
solver.add(Or(day != 1, Or(start_time < 750, start_time >= 870)))
solver.add(Or(day != 1, Or(start_time < 930, start_time >= 960)))

# Wednesday: 10:00-11:30, 12:00-14:00, 14:30-17:00
solver.add(Or(day != 2, Or(start_time < 600, start_time >= 690)))
solver.add(Or(day != 2, Or(start_time < 720, start_time >= 840)))
solver.add(Or(day != 2, Or(start_time < 870, start_time >= 1020)))

# Stephanie would like to avoid more meetings on Monday
solver.add(day != 0)

# Betty can not meet on Tuesday after 12:30
solver.add(Or(day != 1, start_time + 60 <= 750))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    day_value = model[day].as_long()
    start_time_value = model[start_time].as_long()
    end_time_value = start_time_value + 60

    # Convert day number to string
    days = ["Monday", "Tuesday", "Wednesday"]
    day_str = days[day_value]

    # Convert time from minutes to HH:MM format
    start_time_str = f"{start_time_value // 60:02}:{start_time_value % 60:02}"
    end_time_str = f"{end_time_value // 60:02}:{end_time_value % 60:02}"

    print(f"SOLUTION:\nDay: {day_str}\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
else:
    print("No solution found")