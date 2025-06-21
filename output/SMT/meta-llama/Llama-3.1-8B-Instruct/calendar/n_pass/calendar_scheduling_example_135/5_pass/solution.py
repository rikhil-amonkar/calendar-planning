from z3 import *

def solve_meeting():
    # Define the day of the week
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday', 'Sunday']
    day = days[0]  # We are only interested in Monday

    # Define the start and end times of the work hours
    start_time = 9 * 60  # 9:00 in minutes
    end_time = 17 * 60  # 17:00 in minutes
    meeting_duration = 30  # 30 minutes

    # Define the existing schedules for each participant
    ashley_busy = [10 * 60, 10 * 60 + 30, 11 * 60, 11 * 60 + 30, 12 * 60 + 30, 12 * 60 + 60, 15 * 60]
    ronald_busy = [9 * 60, 9 * 60 + 30, 10 * 60, 10 * 60 + 30, 12 * 60 + 30, 12 * 60 + 60, 14 * 60 + 30, 14 * 60 + 60, 16 * 60, 16 * 60 + 30, 16 * 60 + 60]
    larry_blocked = [9 * 60, 9 * 60 + 30, 10 * 60, 10 * 60 + 30, 11 * 60, 11 * 60 + 30, 13 * 60, 13 * 60 + 30, 14 * 60, 14 * 60 + 30, 15 * 60, 15 * 60 + 30, 16 * 60, 16 * 60 + 30, 16 * 60 + 60]

    # Define the variables for the start time of the meeting
    start_time_var = Int('start_time')

    # Define the constraints for the meeting
    constraints = [
        And(start_time_var >= start_time, start_time_var + 30 < end_time),
        Or(start_time_var + 30 > ashley_busy[i] for i in range(len(ashley_busy))),
        Or(start_time_var + 30 > ronald_busy[i] for i in range(len(ronald_busy))),
        Or(start_time_var + 30 > larry_blocked[i] for i in range(len(larry_blocked))),
        start_time_var % 30 == 0,  # The start time must be a multiple of 30 minutes
        start_time_var + 30 <= 17 * 60  # The end time must be before 17:00
    ]

    # Solve the constraints
    solver = Solver()
    solver.add(constraints)
    if solver.check() == sat:
        model = solver.model()
        start_time = model[start_time_var].as_long()
        print(f'Day: {day}')
        print(f'Start Time: {start_time // 60:02d}:{start_time % 60:02d}')
        print(f'End Time: {(start_time // 60 + 1) * 60:02d}:{((start_time // 60 + 1) * 60) % 60:02d}')
    else:
        print('No solution found')

solve_meeting()