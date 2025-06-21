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
    constraints.append(start_time >= 9 + day * 24)
    constraints.append(end_time <= 17 + day * 24)

    # Add constraints for the meeting time in 30-minute intervals
    possible_times = [9.5, 10, 10.5, 11, 11.5, 12, 12.5, 13, 13.5, 14, 14.5, 15, 15.5, 16, 16.5]
    start_time_var = Int('start_time')
    end_time_var = Int('end_time')
    solver = Solver()
    for variable in variables:
        solver.add(variable)
    for i, time in enumerate(possible_times):
        solver.add(start_time_var == time)
        solver.add(end_time_var == time + 0.5)
        solver.add(And(constraints))
        if solver.check() == sat:
            model = solver.model()
            return f"SOLUTION:\nDay: {['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday'][day]}\nStart Time: {int(time.as_real().numerator / 60):02d}:00\nEnd Time: {int((time + 0.5).as_real().numerator / 60):02d}:30"
        solver.add(Not(start_time_var == time))
        solver.add(Not(end_time_var == time + 0.5))

    return "No solution found"

# Example usage
schedules = {
    'Patrick': [(9, 9.5), (10, 10.5), (13.5, 14), (16, 16.5)],
    'Kayla': [(12.5, 13.5), (15, 15.5), (16, 16.5)],
    'Carl': [(10.5, 11), (12, 12.5), (13, 13.5), (14.5, 17)],
    'Christian': [(9, 12.5), (13, 14), (14.5, 17)]
}

print(schedule_meeting(0, 0, 0, schedules))