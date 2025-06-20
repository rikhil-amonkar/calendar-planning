from z3 import *

def schedule_meeting():
    # Define the day of the meeting
    day = 'Monday'

    # Define the start and end times for the meeting
    start_time = Int('start_time')
    end_time = Int('end_time')

    # Define the constraints for each participant
    wayne_free = [And(start_time >= 9, start_time <= 17),
                  And(end_time >= 9, end_time <= 17)]

    melissa_busy = [And(start_time >= 10, start_time < 11),
                    And(start_time >= 12.5, start_time < 14),
                    And(start_time >= 15, start_time < 15.5)]

    catherine_free = [And(start_time >= 9, start_time <= 17)]

    gregory_busy = [And(start_time >= 12.5, start_time < 13),
                    And(start_time >= 15.5, start_time < 16)]

    victoria_busy = [And(start_time >= 9, start_time < 9.5),
                     And(start_time >= 10.5, start_time < 11.5),
                     And(start_time >= 13, start_time < 14),
                     And(start_time >= 14.5, start_time < 15),
                     And(start_time >= 15.5, start_time < 16.5)]

    thomas_busy = [And(start_time >= 10, start_time < 12),
                   And(start_time >= 12.5, start_time < 13),
                   And(start_time >= 14.5, start_time < 16)]

    jennifer_busy = [And(start_time >= 9, start_time < 9.5),
                     And(start_time >= 10, start_time < 10.5),
                     And(start_time >= 11, start_time < 13),
                     And(start_time >= 13.5, start_time < 14.5),
                     And(start_time >= 15, start_time < 15.5),
                     And(start_time >= 16, start_time < 16.5)]

    # Wayne's preference to avoid meetings before 14:00
    wayne_preference = start_time >= 14

    # Meeting duration is 30 minutes
    meeting_duration = 0.5

    # Define the solver
    solver = Solver()

    # Add constraints to the solver
    solver.add(And(wayne_free, melissa_busy, catherine_free, gregory_busy,
                   victoria_busy, thomas_busy, jennifer_busy, wayne_preference,
                   start_time + meeting_duration == end_time, start_time >= 9,
                   start_time <= 17))

    # Solve the constraints
    if solver.check() == sat:
        model = solver.model()
        start_time_value = model[start_time].as_real().numeral().as_decimal().value()
        end_time_value = model[end_time].as_real().numeral().as_decimal().value()
        print(f'SOLUTION:\nDay: {day}\nStart Time: {int(start_time_value * 100) // 100:02d}:{int((start_time_value * 100) % 100):02d}')
        print(f'End Time: {int(end_time_value * 100) // 100:02d}:{int((end_time_value * 100) % 100):02d}')
    else:
        print('No solution found')

schedule_meeting()