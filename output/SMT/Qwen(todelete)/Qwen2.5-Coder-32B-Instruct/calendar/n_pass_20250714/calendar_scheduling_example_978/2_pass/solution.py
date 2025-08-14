from z3 import *

# Define the days of the week as integers
monday, tuesday, wednesday, thursday, friday = 0, 1, 2, 3, 4

# Define the participants' schedules
brian_schedule = {
    monday: [(930, 1000), (1230, 1430), (1530, 1600)],
    tuesday: [(900, 930)],
    wednesday: [(1230, 1400), (1630, 1700)],
    thursday: [(1100, 1130), (1300, 1330), (1630, 1700)],
    friday: [(930, 1000), (1030, 1100), (1300, 1330), (1500, 1600), (1630, 1700)]
}

julia_schedule = {
    monday: [(900, 1000), (1100, 1130), (1230, 1300), (1530, 1600)],
    tuesday: [(1300, 1400), (1600, 1630)],
    wednesday: [(900, 1130), (1200, 1230), (1300, 1700)],
    thursday: [(900, 1030), (1100, 1700)],
    friday: [(900, 1000), (1030, 1130), (1230, 1400), (1430, 1500), (1530, 1600)]
}

# Create a Z3 solver
solver = Solver()

# Define variables
day = Int('day')
start_time = Int('start_time')

# Constraints for the day and start time
solver.add(day >= 0)
solver.add(day <= 4)
solver.add(start_time >= 900)
solver.add(start_time <= 1600)

# Define the meeting duration
meeting_duration = 100

# Add constraints for Brian's schedule
for d, slots in brian_schedule.items():
    for s, e in slots:
        solver.add(Or(day != d, Or(start_time + meeting_duration <= s, start_time >= e)))

# Add constraints for Julia's schedule
for d, slots in julia_schedule.items():
    for s, e in slots:
        solver.add(Or(day != d, Or(start_time + meeting_duration <= s, start_time >= e)))

# Check for available times on days other than Monday first
days_to_check = [tuesday, wednesday, thursday, friday, monday]

for d in days_to_check:
    solver.push()
    solver.add(day == d)
    if solver.check() == sat:
        model = solver.model()
        day_value = model[day].as_long()
        start_time_value = model[start_time].as_long()
        end_time_value = start_time_value + meeting_duration
        
        # Convert day number to string
        days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
        day_str = days[day_value]
        
        # Convert time to HH:MM format
        start_time_str = f"{start_time_value // 100:02}:{start_time_value % 100:02}"
        end_time_str = f"{end_time_value // 100:02}:{end_time_value % 100:02}"
        
        print(f"SOLUTION:\nDay: {day_str}\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
        break
    solver.pop()