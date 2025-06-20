from z3 import *

def schedule_meeting():
    # Define the variables
    day = Int('day')
    start_time = Int('start_time')
    end_time = Int('end_time')

    # Define the constraints
    # Russell is busy on Monday during 10:30 to 11:00
    russell_busy_monday = And(day == 1, start_time >= 10*60 + 30, start_time < 11*60 + 30)
    # Russell is busy on Tuesday during 13:00 to 13:30
    russell_busy_tuesday = And(day == 2, start_time >= 13*60, start_time < 13*60 + 30)
    # Alexander has meetings on Monday during 9:00 to 11:30, 12:00 to 14:30, 15:00 to 17:00
    alexander_busy_monday = Or(And(day == 1, start_time >= 9*60, start_time < 11*60 + 30),
                               And(day == 1, start_time >= 12*60, start_time < 14*60 + 30),
                               And(day == 1, start_time >= 15*60, start_time < 17*60))
    # Alexander has meetings on Tuesday during 9:00 to 10:00, 13:00 to 14:00, 15:00 to 15:30, 16:00 to 16:30
    alexander_busy_tuesday = Or(And(day == 2, start_time >= 9*60, start_time < 10*60),
                                And(day == 2, start_time >= 13*60, start_time < 13*60 + 30),  # Changed to 13:30
                                And(day == 2, start_time >= 15*60, start_time < 15*60 + 30),
                                And(day == 2, start_time >= 16*60, start_time < 16*60 + 30))
    # Russell would rather not meet on Tuesday before 13:30
    russell_not_tuesday_before_1330 = And(day == 2, start_time >= 13*60)

    # Russell and Alexander are available on Monday during 11:00 to 12:00 and 14:30 to 15:00
    russell_available_monday = And(day == 1, start_time >= 11*60, start_time < 12*60)
    alexander_available_monday = And(day == 1, start_time >= 14*60 + 30, start_time < 15*60)
    # Russell and Alexander are available on Tuesday during 10:00 to 12:59 and 14:00 to 17:00
    russell_available_tuesday = And(day == 2, start_time >= 10*60, start_time < 12*60 + 59)
    alexander_available_tuesday = And(day == 2, start_time >= 10*60, start_time < 12*60 + 59)  # Changed to 12:59
    alexander_available_tuesday_2 = And(day == 2, start_time >= 14*60, start_time < 17*60)

    # The meeting duration is one hour
    meeting_duration = And(end_time - start_time == 60)

    # The start and end time must be within the work hours
    work_hours = And(start_time >= 9*60, start_time < 17*60, end_time >= 9*60, end_time < 17*60)

    # Combine all the constraints
    constraints = And(
        day >= 1,
        day <= 2,
        russell_busy_monday == False,
        russell_busy_tuesday == False,
        alexander_busy_monday == False,
        alexander_busy_tuesday == False,
        russell_not_tuesday_before_1330 == False,
        russell_available_monday == False,
        alexander_available_monday == False,
        russell_available_tuesday == False,
        alexander_available_tuesday == False,
        alexander_available_tuesday_2 == False,
        meeting_duration,
        work_hours
    )

    # Solve the constraints
    solver = Solver()
    solver.add(constraints)
    if solver.check() == sat:
        model = solver.model()
        day_value = model[day].as_long()
        start_time_value = model[start_time].as_long()
        end_time_value = model[end_time].as_long()
        day_str = 'Monday' if day_value == 1 else 'Tuesday'
        start_time_str = f'{start_time_value // 60:02d}:{start_time_value % 60:02d}'
        end_time_str = f'{end_time_value // 60:02d}:{end_time_value % 60:02d}'
        return f'SOLUTION:\nDay: {day_str}\nStart Time: {start_time_str}\nEnd Time: {end_time_str}'
    else:
        return 'No solution found'

print(schedule_meeting())