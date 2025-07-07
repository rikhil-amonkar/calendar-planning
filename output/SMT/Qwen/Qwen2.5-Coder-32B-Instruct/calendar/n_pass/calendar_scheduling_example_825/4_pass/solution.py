from z3 import *

# Define the days of the week as integers
Monday, Tuesday, Wednesday, Thursday = 0, 1, 2, 3

# Define the time slots in one-hour increments from 9:00 to 17:00
time_slots = list(range(9))  # 9:00 to 16:00 (9 one-hour slots)

# Define the variables for the day and time slot
day = Int('day')
start_time_slot = Int('start_time_slot')

# Define the constraints
constraints = [
    # Day must be one of Monday, Tuesday, Wednesday, or Thursday
    And(day >= Monday, day <= Thursday),
    
    # Start time must be within working hours (9:00 to 16:00) to allow for a 1-hour meeting
    And(start_time_slot >= 0, start_time_slot <= 8),  # 8 because 16:00 is the latest start time for a 1-hour meeting
    
    # Laura's availability
    Or(
        # Monday
        Not(And(day == Monday, And(start_time_slot >= 1, start_time_slot < 2))),  # 10:00 to 11:00
        Not(And(day == Monday, And(start_time_slot >= 3, start_time_slot < 4))),  # 12:00 to 13:00
        Not(And(day == Monday, And(start_time_slot >= 5, start_time_slot < 6))),  # 14:00 to 15:00
        Not(And(day == Monday, And(start_time_slot >= 7, start_time_slot < 8))),  # 16:00 to 17:00
        # Tuesday
        Not(And(day == Tuesday, And(start_time_slot >= 1, start_time_slot < 2))),  # 10:00 to 11:00
        Not(And(day == Tuesday, And(start_time_slot >= 3, start_time_slot < 4))),  # 12:00 to 13:00
        Not(And(day == Tuesday, And(start_time_slot >= 5, start_time_slot < 6))),  # 14:00 to 15:00
        Not(And(day == Tuesday, And(start_time_slot >= 7, start_time_slot < 8))),  # 16:00 to 17:00
        # Wednesday
        Not(And(day == Wednesday, And(start_time_slot >= 2, start_time_slot < 3))),  # 11:00 to 12:00
        Not(And(day == Wednesday, And(start_time_slot >= 3, start_time_slot < 4))),  # 12:00 to 13:00
        Not(And(day == Wednesday, And(start_time_slot >= 6, start_time_slot < 7))),  # 15:00 to 16:00
        # Thursday
        Not(And(day == Thursday, And(start_time_slot >= 1, start_time_slot < 2))),  # 10:00 to 11:00
        Not(And(day == Thursday, And(start_time_slot >= 3, start_time_slot < 5))),  # 12:00 to 14:00
        Not(And(day == Thursday, And(start_time_slot >= 6, start_time_slot < 7))),  # 15:00 to 16:00
        Not(And(day == Thursday, And(start_time_slot >= 7, start_time_slot < 8)))   # 16:00 to 17:00
    ),
    
    # Philip's availability
    Or(
        # Monday
        False,  # Unavailable all day
        # Tuesday
        Not(And(day == Tuesday, And(start_time_slot >= 0, start_time_slot < 2))),  # 9:00 to 11:00
        Not(And(day == Tuesday, And(start_time_slot >= 3, start_time_slot < 4))),  # 12:00 to 13:00
        Not(And(day == Tuesday, And(start_time_slot >= 5, start_time_slot < 6))),  # 14:00 to 15:00
        Not(And(day == Tuesday, And(start_time_slot >= 6, start_time_slot < 8))),  # 15:00 to 17:00
        # Wednesday
        False,  # Unavailable all day
        # Thursday
        Not(And(day == Thursday, And(start_time_slot >= 0, start_time_slot < 2))),  # 9:00 to 11:00
        Not(And(day == Thursday, And(start_time_slot >= 3, start_time_slot < 5))),  # 12:00 to 14:00
        Not(And(day == Thursday, And(start_time_slot >= 6, start_time_slot < 8)))   # 15:00 to 17:00
    ),
    
    # Philip cannot meet on Wednesday
    day != Wednesday
]

# Create the solver
solver = Solver()
solver.add(constraints)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    day_value = model[day].as_long()
    start_time_slot_value = model[start_time_slot].as_long()
    
    # Convert day value to string
    days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
    day_str = days[day_value]
    
    # Convert time slot value to start time
    start_hour = 9 + start_time_slot_value
    start_minute = 0
    start_time_str = f"{start_hour:02}:{start_minute:02}"
    
    # Calculate end time
    end_hour = start_hour + 1
    end_minute = 0
    end_time_str = f"{end_hour:02}:{end_minute:02}"
    
    # Print the solution
    print(f"SOLUTION:\nDay: {day_str}\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
else:
    print("No solution found")