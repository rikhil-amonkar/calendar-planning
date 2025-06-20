from z3 import *

def schedule_meeting(martha_schedule, beverly_schedule, meeting_duration):
    # Define the days of the week
    days = ['Monday', 'Tuesday', 'Wednesday']

    # Define the time slots for each day
    time_slots = {}
    for day in days:
        time_slots[day] = []
        for hour in range(9, 17):
            for minute in range(0, 60, 30):
                start_time = f"{hour:02d}:{minute:02d}"
                end_time = f"{hour + 1 if minute!= 30 else hour:02d}:{60 if minute!= 30 else 0}"
                time_slots[day].append((start_time, end_time))

    # Define the variables
    day = Int('day')
    start_time = Int('start_time')
    end_time = Int('end_time')

    # Define the constraints
    day_domain = [0, 1, 2]  # Monday, Tuesday, Wednesday
    start_time_domain = [f"{hour:02d}:{minute:02d}" for hour in range(9, 17) for minute in range(0, 60, 30)]
    end_time_domain = [f"{hour:02d}:{minute:02d}" for hour in range(9, 17) for minute in range(0, 60, 30)]
    constraints = [
        day >= 0,
        day <= 2,
        start_time >= '09:00',
        start_time <= '16:30',
        end_time >= start_time,
        end_time <= '17:00',
        start_time + '30' in martha_schedule[day],
        start_time + '30' in beverly_schedule[day],
        (start_time + '30' in martha_schedule[day]) == (start_time + '30' in beverly_schedule[day]),
        (start_time + '00' in martha_schedule[day]) == (start_time + '00' in beverly_schedule[day]),
        start_time + meeting_duration <= '17:00'
    ]

    # Add constraints for Martha's schedule
    for i, (start, end) in enumerate(time_slots[days[day]]):
        constraints.append(start_time!= start)
        constraints.append(end_time!= end)

    # Add constraints for Beverly's schedule
    for i, (start, end) in enumerate(time_slots[days[day]]):
        constraints.append(start_time!= start)
        constraints.append(end_time!= end)

    # Solve the problem
    solver = Solver()
    solver.add(constraints)
    solution = solver.check()

    # Print the solution
    if solution == sat:
        model = solver.model()
        day_value = model[day].as_long()
        start_time_value = model[start_time].as_string()
        end_time_value = model[end_time].as_string()
        print(f"SOLUTION:")
        print(f"Day: {days[day_value]}")
        print(f"Start Time: {start_time_value}")
        print(f"End Time: {end_time_value}")
    else:
        print("No solution found.")

# Define the schedules
martha_schedule = {
    'Monday': ['09:00:00-09:30:00', '09:30:00-10:00:00', '10:00:00-11:00:00', '11:00:00-12:00:00', '12:00:00-13:00:00', '13:00:00-14:00:00', '14:00:00-14:30:00', '14:30:00-15:00:00', '15:00:00-15:30:00', '15:30:00-16:00:00', '16:00:00-17:00:00'],
    'Tuesday': ['09:00:00-09:30:00', '09:30:00-10:00:00', '10:00:00-11:00:00', '11:00:00-12:00:00', '12:00:00-13:00:00', '13:00:00-14:00:00', '14:00:00-14:30:00', '14:30:00-15:00:00', '15:00:00-15:30:00'],
    'Wednesday': ['09:00:00-09:30:00', '09:30:00-10:00:00', '10:00:00-11:00:00', '11:00:00-12:00:00', '12:00:00-13:00:00', '13:00:00-14:00:00', '14:00:00-14:30:00', '14:30:00-15:00:00']
}

beverly_schedule = {
    'Monday': ['09:00:00-13:30:00', '13:30:00-14:00:00', '14:00:00-17:00:00'],
    'Tuesday': ['09:00:00-17:00:00'],
    'Wednesday': ['09:30:00-10:00:00', '10:00:00-11:00:00', '11:00:00-12:00:00', '12:00:00-13:00:00', '13:00:00-14:00:00', '14:00:00-14:30:00', '14:30:00-15:30:00', '15:30:00-16:00:00', '16:00:00-16:30:00', '16:30:00-17:00:00']
}

meeting_duration = '01:00'

schedule_meeting(martha_schedule, beverly_schedule, meeting_duration)