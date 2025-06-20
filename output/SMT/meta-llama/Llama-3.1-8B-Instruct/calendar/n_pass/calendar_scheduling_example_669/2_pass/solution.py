from z3 import *

def schedule_meeting(jean_schedule, doris_schedule, doris_preference):
    # Define the days of the week
    days = ['Monday', 'Tuesday']

    # Define the time slots for the meeting
    start_time = 9
    end_time = 17
    time_slots = [f'{hour:02d}:00' for hour in range(start_time, end_time + 1)]
    time_slots += [f'{hour:02d}:30' for hour in range(start_time, end_time + 1)]

    # Define the meeting duration
    meeting_duration = 0.5

    # Create Z3 variables for the day, start time, and end time
    day = Int('day')
    start = Int('start')
    end = Int('end')

    # Define the constraints for the day
    day_domain = [day == day_val for day_val in range(len(days))]
    day_domain += [day >= 0, day < len(days)]

    # Define the constraints for the start and end times
    time_domain = [start >= 0, start < len(time_slots), end >= 0, end < len(time_slots)]
    time_domain += [start <= end]
    time_domain += [end - start == int(meeting_duration * 2)]

    # Define the constraints for the schedules
    jean_constraints = []
    for time in jean_schedule:
        jean_constraints += [start!= time[0], start!= time[1], end!= time[0], end!= time[1]]
    doris_constraints = []
    for time in doris_schedule:
        doris_constraints += [start!= time[0], start!= time[1], end!= time[0], end!= time[1]]
    if doris_preference:
        doris_constraints += [start >= 14]

    # Define the constraints for the solver
    constraints = day_domain + time_domain + jean_constraints + doris_constraints

    # Create the solver
    solver = Solver()

    # Add the constraints to the solver
    for constraint in constraints:
        solver.add(constraint)

    # Check if the solver has a solution
    if solver.check() == sat:
        # Get the model from the solver
        model = solver.model()

        # Get the values of the day, start time, and end time from the model
        day_val = days[model[day].as_long()]
        start_val = time_slots[model[start].as_long()]
        end_val = time_slots[model[end].as_long()]

        # Return the solution
        return f'SOLUTION:\nDay: {day_val}\nStart Time: {start_val}\nEnd Time: {end_val}'
    else:
        # If no solution is found, try to find a solution that works on Monday
        # Define the constraints for Monday
        day_domain = [day == 0]
        time_domain = [start >= 0, start < len(time_slots), end >= 0, end < len(time_slots)]
        time_domain += [start <= end]
        time_domain += [end - start == int(meeting_duration * 2)]
        jean_constraints = []
        for time in jean_schedule:
            jean_constraints += [start!= time[0], start!= time[1], end!= time[0], end!= time[1]]
        doris_constraints = []
        for time in doris_schedule:
            doris_constraints += [start!= time[0], start!= time[1], end!= time[0], end!= time[1]]
        doris_constraints += [start >= 14]

        # Define the constraints for the solver
        constraints = day_domain + time_domain + jean_constraints + doris_constraints

        # Create the solver
        solver = Solver()

        # Add the constraints to the solver
        for constraint in constraints:
            solver.add(constraint)

        # Check if the solver has a solution
        if solver.check() == sat:
            # Get the model from the solver
            model = solver.model()

            # Get the values of the day, start time, and end time from the model
            day_val = days[model[day].as_long()]
            start_val = time_slots[model[start].as_long()]
            end_val = time_slots[model[end].as_long()]

            # Return the solution
            return f'SOLUTION:\nDay: {day_val}\nStart Time: {start_val}\nEnd Time: {end_val}'
        else:
            # If no solution is found, try to find a solution that works on Tuesday
            # Define the constraints for Tuesday
            day_domain = [day == 1]
            time_domain = [start >= 0, start < len(time_slots), end >= 0, end < len(time_slots)]
            time_domain += [start <= end]
            time_domain += [end - start == int(meeting_duration * 2)]
            jean_constraints = []
            for time in jean_schedule:
                jean_constraints += [start!= time[0], start!= time[1], end!= time[0], end!= time[1]]
            doris_constraints = []
            for time in doris_schedule:
                doris_constraints += [start!= time[0], start!= time[1], end!= time[0], end!= time[1]]

            # Define the constraints for the solver
            constraints = day_domain + time_domain + jean_constraints + doris_constraints

            # Create the solver
            solver = Solver()

            # Add the constraints to the solver
            for constraint in constraints:
                solver.add(constraint)

            # Check if the solver has a solution
            if solver.check() == sat:
                # Get the model from the solver
                model = solver.model()

                # Get the values of the day, start time, and end time from the model
                day_val = days[model[day].as_long()]
                start_val = time_slots[model[start].as_long()]
                end_val = time_slots[model[end].as_long()]

                # Return the solution
                return f'SOLUTION:\nDay: {day_val}\nStart Time: {start_val}\nEnd Time: {end_val}'
            else:
                return 'No solution found'

# Example usage
jean_schedule = [(11, 12), (16, 17)]
doris_schedule = [(9, 11), (12, 12.5), (13.5, 16), (16.5, 17), (9, 17)]
doris_preference = True

print(schedule_meeting(jean_schedule, doris_schedule, doris_preference))