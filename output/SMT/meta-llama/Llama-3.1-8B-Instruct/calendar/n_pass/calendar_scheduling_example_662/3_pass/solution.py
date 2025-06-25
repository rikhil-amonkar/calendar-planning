from z3 import *

def schedule_meeting(gary_schedule, david_schedule, meeting_duration):
    # Create Z3 variables for day and time
    day = Int('day')
    start_time = Real('start_time')
    end_time = Real('end_time')

    # Define the day variable
    day_domain = If(day == 0, 9, 10)  # 0 for Monday, 1 for Tuesday
    day_range = [0, 1]

    # Define the start and end time variables
    start_time_domain = If(day == 0, 9, 9) + If(start_time >= 9, 0, 1)
    end_time_domain = If(day == 0, 17, 17) - meeting_duration

    # Create Z3 constraints
    constraints = [
        And(day_domain >= 0, day_domain < 2),  # day is either 0 (Monday) or 1 (Tuesday)
        And(start_time_domain >= 9, start_time_domain < 17),  # start time is between 9:00 and 16:59
        And(end_time_domain >= 9, end_time_domain < 17),  # end time is between 9:00 and 16:59
        Implies(day == 0, start_time!= 9.5),  # if day is Monday, start time cannot be 9:30
        Implies(day == 0, start_time!= 11, end_time!= 13),  # if day is Monday, start time cannot be 11:00 and end time cannot be 13:00
        Implies(day == 0, start_time!= 14, end_time!= 14.5),  # if day is Monday, start time cannot be 14:00 and end time cannot be 14:30
        Implies(day == 0, start_time!= 16.5, end_time!= 17),  # if day is Monday, start time cannot be 16:30 and end time cannot be 17:00
        Implies(day == 1, start_time!= 9, end_time!= 9.5),  # if day is Tuesday, start time cannot be 9:00 and end time cannot be 9:30
        Implies(day == 1, start_time!= 10.5, end_time!= 11),  # if day is Tuesday, start time cannot be 10:30 and end time cannot be 11:00
        Implies(day == 1, start_time!= 14.5, end_time!= 16),  # if day is Tuesday, start time cannot be 14:30 and end time cannot be 16:00
        start_time + meeting_duration == end_time,  # meeting duration is 1 hour
    ]

    # Add Gary's schedule constraints
    for i in range(len(gary_schedule)):
        gary_start = gary_schedule[i][0]
        gary_end = gary_schedule[i][1]
        constraints.append(Or(
            day!= 0 or (day == 0 and start_time < gary_start),
            day!= 0 or (day == 0 and start_time + meeting_duration >= gary_end)
        ))

    # Add David's schedule constraints
    for i in range(len(david_schedule)):
        david_start = david_schedule[i][0]
        david_end = david_schedule[i][1]
        constraints.append(Or(
            day!= 1 or (day == 1 and start_time < david_start),
            day!= 1 or (day == 1 and start_time + meeting_duration >= david_end)
        ))

    # Solve the Z3 constraints
    solver = Solver()
    solver.add(constraints)
    if solver.check() == sat:
        model = solver.model()
        day_value = int(model[day])
        start_time_value = model[start_time].as_real().numerator()
        end_time_value = model[end_time].as_real().numerator()
        print(f'Day: {["Monday", "Tuesday"][day_value]}')
        print(f'Start Time: {start_time_value:.1f}:00')
        print(f'End Time: {(start_time_value + 1):.1f}:00')
    else:
        print('No solution found')

# Example usage
gary_schedule = [(9.5, 10), (11, 13), (14, 14.5), (16.5, 17), (9, 9.5), (10.5, 11), (14.5, 16)]
david_schedule = [(9, 9.5), (10, 10.5), (11, 12.5), (13, 14.5), (15, 16), (16.5, 17), (9, 9.5), (10, 10.5), (11, 12.5), (13, 14.5), (15, 16), (16.5, 17)]
schedule_meeting(gary_schedule, david_schedule, 1)