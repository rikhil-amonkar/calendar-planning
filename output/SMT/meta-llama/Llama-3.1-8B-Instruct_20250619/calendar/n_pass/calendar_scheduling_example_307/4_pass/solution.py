from z3 import *

def schedule_meeting():
    # Define the variables
    day = 'Monday'
    start_time = Int('start_time')
    end_time = Int('end_time')
    meeting_duration = 30  # Meeting duration in minutes

    # Define the constraints for each participant
    stephen_blocked = Or(And(start_time >= 10, start_time < 10 + 30), And(start_time >= 12, start_time < 12 + 30))
    brittany_blocked = Or(And(start_time >= 11, start_time < 11 + 30), And(start_time >= 13 + 30, start_time < 14), And(start_time >= 15 + 30, start_time < 16), And(start_time >= 16 + 30, start_time < 17))
    dorothy_blocked = Or(And(start_time >= 9, start_time < 9 + 30), And(start_time >= 10, start_time < 10 + 30), And(start_time >= 11, start_time < 12 + 30), And(start_time >= 13, start_time < 15), And(start_time >= 15 + 30, start_time < 17))
    rebecca_blocked = Or(And(start_time >= 9 + 30, start_time < 10 + 30), And(start_time >= 11, start_time < 11 + 30), And(start_time >= 12, start_time < 12 + 30), And(start_time >= 13, start_time < 17))
    jordan_blocked = Or(And(start_time >= 9, start_time < 9 + 30), And(start_time >= 10, start_time < 11), And(start_time >= 11 + 30, start_time < 12), And(start_time >= 13, start_time < 15), And(start_time >= 15 + 30, start_time < 16 + 30))

    # Define the constraints for the meeting duration
    meeting_constraints = And(start_time + meeting_duration <= 17 * 60)

    # Define the solver
    solver = Solver()

    # Add the constraints to the solver
    solver.add(And(day == 'Monday', start_time >= 9 * 60, start_time < 17 * 60))
    solver.add(Not(stephen_blocked))
    solver.add(Not(brittany_blocked))
    solver.add(Not(dorothy_blocked))
    solver.add(Not(rebecca_blocked))
    solver.add(Not(jordan_blocked))
    solver.add(meeting_constraints)

    # Solve the constraints
    if solver.check() == sat:
        model = solver.model()
        start_time_value = model[start_time].as_long()
        end_time_value = start_time_value + meeting_duration
        return f'SOLUTION:\nDay: {day}\nStart Time: {str(start_time_value // 60).zfill(2)}:{str(start_time_value % 60).zfill(2)}\nEnd Time: {str((start_time_value + meeting_duration) // 60).zfill(2)}:{str((start_time_value + meeting_duration) % 60).zfill(2)}'
    else:
        # If no solution is found, try to find a solution by iterating over possible start times
        for start_time_value in range(9 * 60 + 30, 17 * 60):
            end_time_value = start_time_value + meeting_duration
            if Not(stephen_blocked.substitute(start_time, start_time_value)).is_true() and Not(brittany_blocked.substitute(start_time, start_time_value)).is_true() and Not(dorothy_blocked.substitute(start_time, start_time_value)).is_true() and Not(rebecca_blocked.substitute(start_time, start_time_value)).is_true() and Not(jordan_blocked.substitute(start_time, start_time_value)).is_true() and (start_time_value + meeting_duration <= 17 * 60):
                return f'SOLUTION:\nDay: {day}\nStart Time: {str(start_time_value // 60).zfill(2)}:{str(start_time_value % 60).zfill(2)}\nEnd Time: {str(end_time_value // 60).zfill(2)}:{str(end_time_value % 60).zfill(2)}'
        return 'No solution found'

print(schedule_meeting())