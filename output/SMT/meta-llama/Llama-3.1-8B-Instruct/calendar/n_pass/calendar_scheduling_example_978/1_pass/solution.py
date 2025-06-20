from z3 import *

def solve_meeting_schedule():
    # Define the days of the week
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']

    # Define the start and end times of the workday
    start_time = 9 * 60
    end_time = 17 * 60

    # Define the duration of the meeting
    meeting_duration = 60

    # Define the variables for the day and start time of the meeting
    day = Int('day')
    start_time_var = Int('start_time')

    # Define the constraints for the day and start time
    day_domain = [If(day == 0, And(start_time_var >= 9 * 60, start_time_var <= 17 * 60), 
                        If(day == 1, And(start_time_var >= 9 * 60, start_time_var <= 17 * 60), 
                         If(day == 2, And(start_time_var >= 9 * 60, start_time_var <= 17 * 60), 
                          If(day == 3, And(start_time_var >= 9 * 60, start_time_var <= 17 * 60), 
                           If(day == 4, And(start_time_var >= 9 * 60, start_time_var <= 17 * 60), 
                            None))))))

    # Define the constraints for Brian's schedule
    brian_schedule = [If(day == 0, 
                          Or(start_time_var < 9 * 60, start_time_var >= 9 * 30, start_time_var >= 12 * 30, start_time_var >= 15 * 30, start_time_var >= 16 * 60),
                          If(day == 1, Or(start_time_var < 9 * 60, start_time_var >= 9 * 60, start_time_var >= 13 * 60, start_time_var >= 16 * 60),
                           If(day == 2, Or(start_time_var < 9 * 60, start_time_var >= 12 * 30, start_time_var >= 16 * 60, start_time_var >= 17 * 60),
                            If(day == 3, Or(start_time_var < 9 * 60, start_time_var >= 11 * 60, start_time_var >= 13 * 60, start_time_var >= 16 * 60, start_time_var >= 17 * 60),
                             If(day == 4, Or(start_time_var < 9 * 60, start_time_var >= 9 * 60, start_time_var >= 10 * 60, start_time_var >= 13 * 60, start_time_var >= 15 * 60, start_time_var >= 16 * 60, start_time_var >= 17 * 60),
                              None)))))

    # Define the constraints for Julia's schedule
    julia_schedule = [If(day == 0, 
                          Or(start_time_var < 9 * 60, start_time_var >= 9 * 60, start_time_var >= 11 * 60, start_time_var >= 12 * 60, start_time_var >= 15 * 60, start_time_var >= 16 * 60),
                          If(day == 1, Or(start_time_var < 9 * 60, start_time_var >= 13 * 60, start_time_var >= 16 * 60, start_time_var >= 16 * 60),
                           If(day == 2, Or(start_time_var < 9 * 60, start_time_var >= 9 * 60, start_time_var >= 12 * 60, start_time_var >= 13 * 60, start_time_var >= 17 * 60),
                            If(day == 3, Or(start_time_var < 9 * 60, start_time_var >= 9 * 60, start_time_var >= 11 * 60, start_time_var >= 17 * 60),
                             If(day == 4, Or(start_time_var < 9 * 60, start_time_var >= 9 * 60, start_time_var >= 10 * 60, start_time_var >= 12 * 60, start_time_var >= 14 * 60, start_time_var >= 15 * 60, start_time_var >= 16 * 60),
                              None)))))

    # Brian would like to avoid more meetings on Monday
    brian_monday_avoid = If(day == 0, start_time_var >= 10 * 60, None)

    # Define the solver
    solver = Solver()

    # Add the constraints to the solver
    solver.add(And(day_domain, brian_schedule, julia_schedule, brian_monday_avoid))
    solver.add(start_time_var + meeting_duration <= end_time)

    # Solve the problem
    if solver.check() == sat:
        # Extract the solution
        model = solver.model()
        day_val = model[day].as_long()
        start_time_val = model[start_time_var].as_long()
        end_time_val = start_time_val + meeting_duration

        # Print the solution
        print(f"SOLUTION: Day: {days[day_val]}")
        print(f"Start Time: {start_time_val // 60:02d}:{start_time_val % 60:02d}")
        print(f"End Time: {end_time_val // 60:02d}:{end_time_val % 60:02d}")
    else:
        print("No solution found")

solve_meeting_schedule()