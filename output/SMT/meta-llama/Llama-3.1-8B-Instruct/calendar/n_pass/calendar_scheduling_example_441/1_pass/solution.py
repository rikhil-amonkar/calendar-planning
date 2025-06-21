from z3 import *

# Define the day of the week (Monday)
day = 'Monday'

# Define the meeting duration (30 minutes)
meeting_duration = 30

# Define the start and end times of the work hours
start_work = 9 * 60
end_work = 17 * 60

# Define the existing schedules for each participant
schedules = {
    'Joan': [(11 * 60 + 30, 12 * 60), (14 * 60 + 30, 15 * 60)],
    'Megan': [(9 * 60, 10 * 60), (14 * 60, 14 * 60 + 30), (16 * 60, 16 * 60 + 30)],
    'Austin': [],
    'Betty': [(9 * 60 + 30, 10 * 60), (11 * 60 + 30, 12 * 60), (13 * 60 + 30, 14 * 60), (16 * 60, 16 * 60 + 30)],
    'Judith': [(9 * 60, 11 * 60), (12 * 60, 13 * 60), (14 * 60, 15 * 60)],
    'Terry': [(9 * 60 + 30, 10 * 60), (11 * 60 + 30, 12 * 60 + 30), (13 * 60, 14 * 60 + 30), (15 * 60, 15 * 60 + 30), (16 * 60, 17 * 60)],
    'Kathryn': [(9 * 60 + 30, 10 * 60), (10 * 60 + 30, 11 * 60), (11 * 60 + 30, 13 * 60), (14 * 60, 16 * 60), (16 * 60 + 30, 17 * 60)]
}

# Create a Z3 solver
solver = Solver()

# Define the start time of the meeting
start_time = Int('start_time')
solver.add(start_time >= start_work)
solver.add(start_time <= end_work - meeting_duration)

# Define the end time of the meeting
end_time = start_time + meeting_duration

# Add constraints for each participant
for participant, schedule in schedules.items():
    for time in schedule:
        solver.add(Or(start_time + meeting_duration > time[0], start_time + meeting_duration < time[1]))

# Check if a solution exists
if solver.check() == sat:
    # Get the solution
    model = solver.model()
    start_hour = model[start_time] // 60
    start_minute = model[start_time] % 60
    end_hour = model[end_time] // 60
    end_minute = model[end_time] % 60
    print(f"SOLUTION: Day: {day}")
    print(f"Start Time: {start_hour:02d}:{start_minute:02d}")
    print(f"End Time: {end_hour:02d}:{end_minute:02d}")
else:
    print("No solution exists")