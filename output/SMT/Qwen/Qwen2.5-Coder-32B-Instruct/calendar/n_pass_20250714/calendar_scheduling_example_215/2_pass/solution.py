from z3 import *

# Define the time slots as integers from 0 to 46 representing 9:00 to 16:30 in 15-minute intervals
time_slot = Int('time_slot')

# Define the constraints for each participant
constraints = []

# Steven is free all day, so no constraints for him

# Roy is free all day, so no constraints for him

# Cynthia's busy times: 9:30-10:30, 11:30-12:00, 13:00-13:30, 15:00-16:00
cynthia_busy_times = [(6, 8), (14, 16), (20, 22), (32, 36)]
for start, end in cynthia_busy_times:
    constraints.append(Or(time_slot < start, time_slot >= end))

# Lauren's busy times: 9:00-9:30, 10:30-11:00, 11:30-12:00, 13:00-13:30, 14:00-14:30, 15:00-15:30, 16:00-17:00
lauren_busy_times = [(0, 2), (6, 8), (14, 16), (20, 22), (24, 26), (32, 34), (40, 48)]
for start, end in lauren_busy_times:
    constraints.append(Or(time_slot < start, time_slot >= end))

# Robert's busy times: 10:30-11:00, 11:30-12:00, 12:30-13:30, 14:00-16:00
robert_busy_times = [(6, 8), (14, 16), (18, 22), (24, 40)]
for start, end in robert_busy_times:
    constraints.append(Or(time_slot < start, time_slot >= end))

# Meeting duration is 30 minutes, so we need to ensure that time_slot + 2 is also free
constraints.append(time_slot >= 0)
constraints.append(time_slot <= 44)  # 44 corresponds to 16:00 to ensure 30 minutes fit within 16:30

# Ensure that the next time slot (time_slot + 2) is also free
constraints.append(Or(time_slot + 2 < 0, time_slot + 2 >= 48))  # This should be adjusted
for start, end in cynthia_busy_times:
    constraints.append(Or(time_slot + 2 < start, time_slot + 2 >= end))
for start, end in lauren_busy_times:
    constraints.append(Or(time_slot + 2 < start, time_slot + 2 >= end))
for start, end in robert_busy_times:
    constraints.append(Or(time_slot + 2 < start, time_slot + 2 >= end))

# Create the solver and add the constraints
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    time_slot_value = model.evaluate(time_slot).as_long()
    
    # Convert time slot back to HH:MM format
    start_hour = 9 + time_slot_value // 4
    start_minute = (time_slot_value % 4) * 15
    end_hour = start_hour + (start_minute + 30) // 60
    end_minute = (start_minute + 30) % 60
    
    start_time = f"{start_hour:02}:{start_minute:02}"
    end_time = f"{end_hour:02}:{end_minute:02}"
    
    print(f"SOLUTION:\nDay: Monday\nStart Time: {start_time}\nEnd Time: {end_time}")
else:
    print("No solution found")