from z3 import *

def schedule_meeting(brian_schedule, julia_schedule, preferred_day=None):
    # Create a Z3 solver
    s = Solver()

    # Define the days and time slots
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']
    time_slots = [9, 10, 11, 12, 13, 14, 15, 16, 17]

    # Define the variables
    day = Int('day')
    start_time = Int('start_time')
    end_time = Int('end_time')

    # Define the constraints
    s.add(day >= 0)
    s.add(day < 5)  # day is an index of the days list
    s.add(start_time >= 9)
    s.add(start_time < 18)
    s.add(end_time >= 9)
    s.add(end_time < 18)
    s.add(end_time > start_time)  # end time is after start time

    # Add constraints based on Brian's schedule
    for day_index, schedule in enumerate(brian_schedule):
        for t in time_slots:
            s.add(Implies(day == day_index, Not(t in schedule)))

    # Add constraints based on Julia's schedule
    for day_index, schedule in enumerate(julia_schedule):
        for t in time_slots:
            s.add(Implies(day == day_index, Not(t in schedule)))

    # Add constraints to find the earliest available time slot
    s.add(Implies(day == 0, And(start_time >= 10, start_time <= 16)))
    s.add(Implies(day == 1, And(start_time >= 9, start_time <= 14)))
    s.add(Implies(day == 2, And(start_time >= 9, start_time <= 16)))
    s.add(Implies(day == 3, And(start_time >= 10, start_time <= 16)))
    s.add(Implies(day == 4, And(start_time >= 9, start_time <= 16)))

    # Add constraints based on the preferred day
    if preferred_day:
        s.add(day == days.index(preferred_day))

    # Add constraints to ensure the meeting duration is 1 hour
    s.add(Implies(day == 0, end_time == start_time + 1))
    s.add(Implies(day == 1, end_time == start_time + 1))
    s.add(Implies(day == 2, end_time == start_time + 1))
    s.add(Implies(day == 3, end_time == start_time + 1))
    s.add(Implies(day == 4, end_time == start_time + 1))

    # Solve the constraints
    if s.check() == sat:
        model = s.model()
        day_value = days[model[day].as_long()]
        start_time_value = model[start_time].as_long()
        end_time_value = model[end_time].as_long()
        return f'SOLUTION:\nDay: {day_value}\nStart Time: {start_time_value:02d}:00\nEnd Time: {end_time_value:02d}:00'
    else:
        return 'No solution found'

# Define the schedules
brian_schedule = [[], [9, 10], [9, 10, 12, 13, 14, 15, 16], [11, 13, 16], [9, 10, 10, 11, 13, 15, 16]]
julia_schedule = [[9, 11, 12, 15, 16], [13, 16], [9, 10, 12, 13, 16], [9, 10, 11, 16], [9, 10, 10, 11, 12, 14, 15, 16]]

# Find a solution
print(schedule_meeting(brian_schedule, julia_schedule, preferred_day='Monday'))