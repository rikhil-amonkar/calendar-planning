from z3 import *

# Define the day of the week (Monday = 0, Sunday = 6)
day_of_week = [0]

# Define the start and end times (9:00 to 17:00)
start_time = 9
end_time = 17

# Define the duration of the meeting (30 minutes)
meeting_duration = 30

# Define the schedules for each participant
schedules = {
    'Lisa': [(9, 10), (10.5, 11.5), (12.5, 13), (16, 16.5)],
    'Bobby': [(9, 9.5), (10, 10.5), (11.5, 12), (15, 15.5)],
    'Randy': [(9.5, 10), (10.5, 11), (11.5, 12.5), (13, 13.5), (14.5, 15.5), (16, 16.5)]
}

# Define the preferences for Bobby (avoid meetings after 15:00)
bobby_preferences = [(15, 17)]

# Create a Z3 solver
solver = Solver()

# Define the variables for the start and end times of the meeting
day = Int('day')
start_hour = Int('start_hour')
start_minute = Int('start_minute')
end_hour = Int('end_hour')
end_minute = Int('end_minute')

# Add constraints for the day of the week
solver.add(day == 0)

# Add constraints for the start and end times
solver.add(start_hour >= start_time)
solver.add(end_hour <= end_time)
solver.add(end_hour == start_hour + meeting_duration // 60)
solver.add(end_minute == start_minute + meeting_duration % 60)

# Add constraints for the schedules of each participant
for participant, participant_schedule in schedules.items():
    for start_hour_p, start_minute_p in participant_schedule:
        solver.add(start_hour >= start_hour_p)
        solver.add(end_hour > start_hour_p)
        solver.add(end_minute > start_minute_p)
    for end_hour_p, end_minute_p in participant_schedule:
        solver.add(end_hour < end_hour_p)
        solver.add(start_hour < end_minute_p)

# Add constraints for Bobby's preferences
for start_hour_p, end_hour_p in bobby_preferences:
    solver.add(end_hour < start_hour_p)

# Add constraints to find a valid time slot
for hour in range(start_time, end_time):
    for minute in range(0, 60):
        if minute + meeting_duration <= 60:
            start_hour_value = hour
            start_minute_value = minute
            end_hour_value = hour + meeting_duration // 60
            end_minute_value = minute + meeting_duration % 60
            # Add constraints for the schedules of each participant
            for participant, participant_schedule in schedules.items():
                for start_hour_p, start_minute_p in participant_schedule:
                    solver.add(start_hour_value >= start_hour_p)
                    solver.add(end_hour_value > start_hour_p)
                    solver.add(end_minute_value > start_minute_p)
                for end_hour_p, end_minute_p in participant_schedule:
                    solver.add(end_hour_value < end_hour_p)
                    solver.add(start_hour_value < end_minute_p)

# Check if there is a solution
if solver.check() == sat:
    # Get the values of the variables
    model = solver.model()
    day_value = model[day].as_long()
    start_hour_value = model[start_hour].as_long()
    start_minute_value = model[start_minute].as_long()
    end_hour_value = model[end_hour].as_long()
    end_minute_value = model[end_minute].as_long()

    # Print the solution
    print('SOLUTION:')
    print(f'Day: {day_of_week[day_value]}')
    print(f'Start Time: {int(start_hour_value):02d}:{int(start_minute_value):02d}')
    print(f'End Time: {int(end_hour_value):02d}:{int(end_minute_value):02d}')
else:
    print('No solution found')