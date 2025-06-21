from z3 import *

def schedule_meeting():
    # Define the variables
    day = Int('day')
    start_time = Int('start_time')
    end_time = Int('end_time')

    # Define the constraints for each participant
    ryan_busy = [9 * 60, 9 * 60 + 30, 12 * 60 + 30, 12 * 60 + 60]  # Start and end time in minutes for Ryan's busy periods
    ruth_busy = []  # Ruth has no meetings
    denise_busy = [9 * 60 + 30, 10 * 60, 12 * 60, 13 * 60, 14 * 60 + 30, 16 * 60 + 30]  # Start and end time in minutes for Denise's busy periods
    denise_no_late = 12 * 60 + 30  # Denise does not want to meet after this time

    # Define the constraints
    constraints = [
        And(day == 1),  # Day is Monday
        And(9 * 60 <= start_time),  # Start time is after 9:00
        And(start_time < 17 * 60),  # Start time is before 17:00
        And(start_time + 60 <= 17 * 60),  # End time is within the day
        Or(start_time + 60 > ryan_busy[0], And(start_time + 60 <= ryan_busy[1], start_time > ryan_busy[0])),  # Ryan is not busy during the meeting
        Or(start_time + 60 > ruth_busy[0], And(start_time + 60 <= ruth_busy[1], start_time > ruth_busy[0])),  # Ruth is not busy during the meeting
        Or(start_time + 60 > denise_busy[0], And(start_time + 60 <= denise_busy[1], start_time > denise_busy[0])),  # Denise is not busy during the meeting
        Or(start_time + 60 > denise_no_late, start_time <= 12 * 60 + 30)  # Denise does not meet after 12:30
    ]

    # Solve the constraints
    solver = Solver()
    solver.add(constraints)
    if solver.check() == sat:
        model = solver.model()
        day_value = model[day].as_long()
        start_time_value = model[start_time].as_long()
        end_time_value = model[start_time].as_long() + 60
        day_str = {1: 'Monday', 2: 'Tuesday', 3: 'Wednesday', 4: 'Thursday', 5: 'Friday', 6: 'Saturday', 7: 'Sunday'}.get(day_value)
        start_time_str = str(timedelta(minutes=start_time_value)).split('.')[0]
        end_time_str = str(timedelta(minutes=end_time_value)).split('.')[0]
        return f'SOLUTION:\nDay: {day_str}\nStart Time: {start_time_str}\nEnd Time: {end_time_str}'
    else:
        return 'No solution found'

print(schedule_meeting())