from z3 import *

def schedule_meeting():
    # Define the day
    day = 'Monday'

    # Define the start and end times
    start_time = 9
    end_time = 17

    # Define the duration of the meeting
    meeting_duration = 0.5

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
    x = [Real(f'x{i}') for i in range(4)]

    # Add the constraints
    for i in range(4):
        s.add(And(9 <= x[i], x[i] <= 17))

    for i in range(4):
        for j in range(4):
            if i!= j:
                s.add(And(x[i] < x[j], x[i] + meeting_duration < x[j]))

    for i in range(4):
        for schedule in raymond_schedule:
            s.add(Or(x[i] < schedule[0], x[i] + meeting_duration < schedule[0], x[i] > schedule[1]))

        for schedule in billy_schedule:
            s.add(Or(x[i] < schedule[0], x[i] + meeting_duration < schedule[0], x[i] > schedule[1]))

        for schedule in donald_schedule:
            s.add(Or(x[i] < schedule[0], x[i] + meeting_duration < schedule[0], x[i] > schedule[1]))

    # Add the constraint for Billy's preference
    for i in range(4):
        s.add(Or(x[i] < billy_preference[0], x[i] + meeting_duration < billy_preference[0], x[i] > billy_preference[1]))

    # Add the constraint for the meeting duration
    s.add(And(x[0] + meeting_duration == x[1], x[1] + meeting_duration == x[2], x[2] + meeting_duration == x[3]))

    # Solve the constraints
    if s.check() == sat:
        model = s.model()
        start_time = int(model[x[0]].as_real().numerator / model[x[0]].as_real().denominator * 60)
        end_time = int(model[x[3]].as_real().numerator / model[x[3]].as_real().denominator * 60)
        return f'SOLUTION:\nDay: {day}\nStart Time: {start_time:02d}:00\nEnd Time: {end_time:02d}:00'
    else:
        # Try to find a solution by iterating over the time slots
        for i in range(9, 17):
            for j in range(i + meeting_duration*60, 17):
                works_for_raymond = True
                works_for_billy = True
                works_for_donald = True
                for schedule in raymond_schedule:
                    if (i < schedule[0] and j > schedule[1]) or (i > schedule[1] and j < schedule[0]):
                        works_for_raymond = False
                        break
                for schedule in billy_schedule:
                    if (i < schedule[0] and j > schedule[1]) or (i > schedule[1] and j < schedule[0]):
                        works_for_billy = False
                        break
                for schedule in donald_schedule:
                    if (i < schedule[0] and j > schedule[1]) or (i > schedule[1] and j < schedule[0]):
                        works_for_donald = False
                        break
                if works_for_raymond and works_for_billy and works_for_donald:
                    return f'SOLUTION:\nDay: {day}\nStart Time: {i:02d}:00\nEnd Time: {j:02d}:00'

        return 'No solution found'

print(schedule_meeting())