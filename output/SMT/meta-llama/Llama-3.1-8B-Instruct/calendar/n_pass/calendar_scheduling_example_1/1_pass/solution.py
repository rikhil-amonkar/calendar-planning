from z3 import *

def schedule_meeting():
    # Define the day
    day = 'Monday'

    # Define the start and end times
    start_time = 9
    end_time = 17

    # Define the duration of the meeting
    meeting_duration = 30

    # Define the existing schedules for each participant
    raymond_schedule = [
        (9, 9.5),
        (11.5, 12),
        (13, 13.5),
        (15, 15.5)
    ]

    billy_schedule = [
        (10, 10.5),
        (12, 13),
        (16.5, 17)
    ]

    donald_schedule = [
        (9, 9.5),
        (10, 11),
        (12, 13),
        (14, 14.5),
        (16, 17)
    ]

    # Define the preferences for Billy
    billy_preference = (15, 17)

    # Create a Z3 solver
    s = Solver()

    # Define the variables
    x = [Int(f'x{i}') for i in range(4)]

    # Add the constraints
    for i in range(4):
        s.add(And(9 <= x[i], x[i] <= 17))

    for i in range(4):
        for j in range(4):
            if i!= j:
                s.add(And(x[i] < x[j], x[i] + 0.5 < x[j]))

    for i in range(4):
        for schedule in raymond_schedule:
            s.add(Or(x[i] < schedule[0], x[i] + 0.5 < schedule[0], x[i] > schedule[1]))

        for schedule in billy_schedule:
            s.add(Or(x[i] < schedule[0], x[i] + 0.5 < schedule[0], x[i] > schedule[1]))

        for schedule in donald_schedule:
            s.add(Or(x[i] < schedule[0], x[i] + 0.5 < schedule[0], x[i] > schedule[1]))

    # Add the constraint for Billy's preference
    for i in range(4):
        s.add(Or(x[i] < billy_preference[0], x[i] + 0.5 < billy_preference[0], x[i] > billy_preference[1]))

    # Add the constraint for the meeting duration
    s.add(And(x[0] + 0.5 == x[1], x[1] + 0.5 == x[2], x[2] + 0.5 == x[3]))

    # Solve the constraints
    if s.check() == sat:
        model = s.model()
        start_time = int(model[x[0]].as_real().numerator / model[x[0]].as_real().denominator * 60)
        end_time = int(model[x[3]].as_real().numerator / model[x[3]].as_real().denominator * 60)
        return f'SOLUTION:\nDay: {day}\nStart Time: {start_time:02d}:00\nEnd Time: {end_time:02d}:00'
    else:
        return 'No solution found'

print(schedule_meeting())