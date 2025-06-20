from z3 import *

def schedule_meeting(gary_schedule, david_schedule, meeting_duration):
    # Create Z3 solver
    solver = Solver()

    # Define variables
    day = Int('day')
    start_time = Int('start_time')
    end_time = Int('end_time')

    # Define constraints
    solver.add(day >= 1)  # day is either 1 (Monday) or 2 (Tuesday)
    solver.add(day <= 2)

    solver.add(9 * 60 <= start_time)  # start time is between 09:00 and 17:00
    solver.add(start_time <= 17 * 60)

    solver.add(end_time - start_time == meeting_duration * 60)  # end time is start time plus meeting duration

    # Gary's constraints
    gary_constraints = [
        (day == 1, start_time + meeting_duration * 60 > 9 * 60, start_time + meeting_duration * 60 < 9 * 60 + 30),
        (day == 1, start_time + meeting_duration * 60 > 11 * 60, start_time + meeting_duration * 60 < 13 * 60),
        (day == 1, start_time + meeting_duration * 60 > 14 * 60, start_time + meeting_duration * 60 < 14 * 60 + 30),
        (day == 1, start_time + meeting_duration * 60 > 16 * 60 - 30, start_time + meeting_duration * 60 <= 17 * 60),
        (day == 2, start_time + meeting_duration * 60 > 9 * 60, start_time + meeting_duration * 60 < 9 * 60 + 30),
        (day == 2, start_time + meeting_duration * 60 > 10 * 60 + 30, start_time + meeting_duration * 60 < 11 * 60),
        (day == 2, start_time + meeting_duration * 60 > 14 * 60 + 30, start_time + meeting_duration * 60 < 16 * 60)
    ]

    for constraint in gary_constraints:
        solver.add(And(constraint))

    # David's constraints
    david_constraints = [
        (day == 1, start_time + meeting_duration * 60 > 9 * 60, start_time + meeting_duration * 60 < 9 * 60 + 30),
        (day == 1, start_time + meeting_duration * 60 > 10 * 60, start_time + meeting_duration * 60 < 13 * 60),
        (day == 1, start_time + meeting_duration * 60 > 14 * 60 + 30, start_time + meeting_duration * 60 < 16 * 60 + 30),
        (day == 2, start_time + meeting_duration * 60 > 9 * 60, start_time + meeting_duration * 60 < 9 * 60 + 30),
        (day == 2, start_time + meeting_duration * 60 > 10 * 60, start_time + meeting_duration * 60 < 10 * 60 + 30),
        (day == 2, start_time + meeting_duration * 60 > 11 * 60, start_time + meeting_duration * 60 < 12 * 60 + 30),
        (day == 2, start_time + meeting_duration * 60 > 13 * 60, start_time + meeting_duration * 60 < 14 * 60 + 30),
        (day == 2, start_time + meeting_duration * 60 > 15 * 60, start_time + meeting_duration * 60 < 16 * 60),
        (day == 2, start_time + meeting_duration * 60 > 16 * 60 + 30, start_time + meeting_duration * 60 <= 17 * 60)
    ]

    for constraint in david_constraints:
        solver.add(And(constraint))

    # Check if there is a solution
    if solver.check() == sat:
        model = solver.model()
        day_value = model[day].as_long()
        start_time_value = model[start_time].as_long()
        end_time_value = model[end_time].as_long()

        # Format output
        day_str = 'Monday' if day_value == 1 else 'Tuesday'
        start_time_str = '{:02d}:{:02d}'.format(start_time_value // 60, start_time_value % 60)
        end_time_str = '{:02d}:{:02d}'.format(end_time_value // 60, end_time_value % 60)

        return 'SOLUTION:\nDay: {}\nStart Time: {}\nEnd Time: {}'.format(day_str, start_time_str, end_time_str)
    else:
        return 'No solution found'

gary_schedule = [(1, 9 * 60, 10 * 60), (1, 11 * 60, 13 * 60), (1, 14 * 60, 14 * 60 + 30), (1, 16 * 60 - 30, 17 * 60), (2, 9 * 60, 9 * 60 + 30), (2, 10 * 60 + 30, 11 * 60), (2, 14 * 60 + 30, 16 * 60)]
david_schedule = [(1, 9 * 60, 9 * 60 + 30), (1, 10 * 60, 13 * 60), (1, 14 * 60 + 30, 16 * 60 + 30), (2, 9 * 60, 9 * 60 + 30), (2, 10 * 60, 10 * 60 + 30), (2, 11 * 60, 12 * 60 + 30), (2, 13 * 60, 14 * 60 + 30), (2, 15 * 60, 16 * 60), (2, 16 * 60 + 30, 17 * 60)]
meeting_duration = 1

print(schedule_meeting(gary_schedule, david_schedule, meeting_duration))