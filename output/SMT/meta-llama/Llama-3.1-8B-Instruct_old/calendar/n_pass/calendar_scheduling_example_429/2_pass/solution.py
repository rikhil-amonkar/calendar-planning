from z3 import *

def schedule_meeting(schedules, meeting_duration):
    # Create a Z3 solver
    s = Solver()

    # Define the day, start time, and end time
    day = 'Monday'
    start_time = 9
    end_time = 17

    # Calculate the total number of time slots
    num_slots = (end_time - start_time) * 2

    # Create a boolean variable for each time slot
    time_slots = [Bool(f'time_slot_{i}') for i in range(num_slots)]

    # Create a boolean variable for the meeting
    meeting = Bool('meeting')

    # Add the constraints that the meeting must be on the same day and within the work hours
    s.add(And([meeting == True], [day == 'Monday'], [start_time * 2 <= Or([time_slot for time_slot in time_slots])], [end_time * 2 > Or([time_slot for time_slot in time_slots])]))

    # Add the constraints that the meeting must not conflict with any existing schedules
    for schedule in schedules:
        if schedule[0] == 'Monday':
            start_slot = int(schedule[1] * 2)
            end_slot = int(schedule[2] * 2)
            s.add(Not(And([meeting == True], [start_slot <= Or([time_slot for time_slot in time_slots])], [end_slot > Or([time_slot for time_slot in time_slots])])))

    # Add the constraint that the meeting must last for the specified duration
    s.add(And([meeting == True], [meeting_duration * 2 <= Or([time_slot for time_slot in time_slots])], [meeting_duration * 2 > Or([time_slot for time_slot in time_slots])]))

    # Solve the constraints
    if s.check() == sat:
        # Get the model
        m = s.model()

        # Find the time slots that are true in the model
        true_time_slots = [i for i, time_slot in enumerate(time_slots) if m.evaluate(time_slot) == True]

        # Calculate the start and end times of the meeting
        start_time_index = min(true_time_slots)
        end_time_index = start_time_index + int(meeting_duration * 2)

        # Calculate the start and end times in 24-hour format
        start_hour = (start_time_index // 2) % 12 + 9
        if start_hour == 12:
            start_hour = 12
        else:
            start_hour = str(start_hour) + ':00'
        end_hour = (end_time_index // 2) % 12 + 9
        if end_hour == 12:
            end_hour = 12
        else:
            end_hour = str(end_hour) + ':00'

        # Return the solution
        return f'SOLUTION:\nDay: {day}\nStart Time: {start_hour}\nEnd Time: {end_hour}'
    else:
        return 'No solution found'

# Define the existing schedules
schedules = [
    (9, 13, 13.5), (16, 16.5),
    (10, 10.5), (12, 13), (14, 14.5),
    (10, 10.5), (15, 15.5),
    (9, 10), (10.5, 12), (13, 13.5), (14.5, 15), (15.5, 17),
    (9, 10), (11, 11.5), (12.5, 13), (14, 14.5), (15.5, 17),
    (9.5, 10.5), (11, 11.5), (12, 12.5), (13, 13.5), (14, 14.5), (16, 17)
]

# Define the meeting duration
meeting_duration = 0.5

# Print the solution
print(schedule_meeting(schedules, meeting_duration))