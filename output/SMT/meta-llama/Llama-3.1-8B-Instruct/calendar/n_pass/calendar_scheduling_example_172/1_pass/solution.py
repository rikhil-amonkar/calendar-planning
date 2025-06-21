from z3 import *

def schedule_meeting(day, start_time, end_time, schedules):
    # Create Z3 variables for each participant's availability
    participants = ['Patrick', 'Kayla', 'Carl', 'Christian']
    variables = [Bool(participant + '_available') for participant in participants]

    # Create Z3 constraints for each participant's schedule
    constraints = []
    for participant, schedule in schedules.items():
        for time in schedule:
            start, end = time
            constraints.append(Not(And(start_time <= start, end <= end_time, variables[participants.index(participant)])))

    # Add constraints for the meeting duration
    constraints.append(start_time + 0.5 <= end_time)

    # Add constraints for the meeting time
    constraints.append(start_time >= 9)
    constraints.append(end_time <= 17)

    # Add constraints for the meeting day
    constraints.append(start_time >= 9 + day * 24)
    constraints.append(end_time <= 17 + day * 24)

    # Solve the constraints
    solver = Solver()
    for variable in variables:
        solver.add(variable)
    solver.add(And(constraints))

    # Check if a solution exists
    if solver.check() == sat:
        model = solver.model()
        start_time_val = int(model[start_time].as_real().numerator / 60)
        end_time_val = int(model[end_time].as_real().numerator / 60)
        return f"SOLUTION:\nDay: {['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday'][day]}\nStart Time: {start_time_val:02d}:00\nEnd Time: {end_time_val:02d}:30"
    else:
        return "No solution found"

# Example usage
schedules = {
    'Patrick': [(9, 9.5), (10, 10.5), (13.5, 14), (16, 16.5)],
    'Kayla': [(12.5, 13.5), (15, 15.5), (16, 16.5)],
    'Carl': [(10.5, 11), (12, 12.5), (13, 13.5), (14.5, 17)],
    'Christian': [(9, 12.5), (13, 14), (14.5, 17)]
}

print(schedule_meeting(0, 0, 0, schedules))