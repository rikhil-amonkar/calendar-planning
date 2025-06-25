from z3 import *

def schedule_meeting(julie_schedule, sean_schedule, lori_schedule, duration):
    # Create Z3 variables
    start_time = Int('start_time')

    # Define constraints
    # Ensure the meeting is within work hours
    solver = Solver()
    solver.add(9*60 <= start_time)
    solver.add(start_time < 17*60)

    # Ensure the meeting duration is one hour
    solver.add(start_time + 60 <= 17*60)

    # Ensure the meeting time does not conflict with existing schedules
    for i in julie_schedule:
        solver.add(start_time + 60 > i)
    for i in sean_schedule:
        solver.add(start_time + 60 > i)
    for i in lori_schedule:
        solver.add(start_time + 60 > i)

    # Find a solution
    if solver.check() == sat:
        model = solver.model()
        start_time_index = model[start_time].as_long()
        start_time_str = str(start_time_index // 60).zfill(2) + ':' + str(start_time_index % 60).zfill(2)
        end_time_str = str((start_time_index // 60 + 1) % 24).zfill(2) + ':' + str(((start_time_index // 60 + 1) % 24 * 60 + (start_time_index % 60) + 1) % 60).zfill(2)
        print('SOLUTION:')
        print('Day: Monday')
        print('Start Time:'+ start_time_str)
        print('End Time:'+ end_time_str)
    else:
        print('No solution found.')

# Existing schedules for everyone during the day
julie_schedule = [9*60, 9*60+30, 11*60, 11*60+30, 12*60, 12*60+30, 13*30, 16*60]
sean_schedule = [9*60, 9*60+30, 13*60, 13*60+30, 15*60, 15*60+30, 16*60, 16*60+30]
lori_schedule = [10*60, 10*60+30, 11*60, 13*60, 15*60+30, 16*60]

# Schedule a meeting for one hour
schedule_meeting(julie_schedule, sean_schedule, lori_schedule, 60)