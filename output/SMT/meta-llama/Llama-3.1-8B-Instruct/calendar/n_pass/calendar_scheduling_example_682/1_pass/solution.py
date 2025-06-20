from z3 import *

def schedule_meeting(available_days, amanda_schedule, nathan_schedule, meeting_duration, amanda_preferences=None):
    # Create Z3 solver
    solver = Solver()

    # Define variables
    day = [Bool(f'day_{i}') for i in range(len(available_days))]
    start_time = [Int(f'start_time_{i}') for i in range(len(available_days))]
    end_time = [Int(f'end_time_{i}') for i in range(len(available_days))]

    # Add constraints for day
    for i in range(len(available_days)):
        solver.add(day[i] == available_days[i])

    # Add constraints for start and end time
    for i in range(len(available_days)):
        solver.add(start_time[i] >= 9)
        solver.add(start_time[i] < 17)
        solver.add(end_time[i] > start_time[i])
        solver.add(end_time[i] <= 17)
        solver.add(start_time[i] + meeting_duration <= 17)

    # Add constraints for amanda's schedule
    for i in range(len(available_days)):
        for j in range(len(amanda_schedule)):
            if amanda_schedule[j][0] == available_days[i]:
                solver.add(start_time[i] + meeting_duration > amanda_schedule[j][1])
                solver.add(start_time[i] < amanda_schedule[j][0])

    # Add constraints for nathan's schedule
    for i in range(len(available_days)):
        for j in range(len(nathan_schedule)):
            if nathan_schedule[j][0] == available_days[i]:
                solver.add(start_time[i] + meeting_duration > nathan_schedule[j][1])
                solver.add(start_time[i] < nathan_schedule[j][0])

    # Add constraints for amanda's preferences
    if amanda_preferences is not None:
        for i in range(len(available_days)):
            if available_days[i] in amanda_preferences and amanda_preferences[available_days[i]] == 'after_11:00':
                solver.add(start_time[i] > 11)

    # Add constraints for nathan's preferences
    if nathan_preferences is not None:
        for i in range(len(available_days)):
            if available_days[i] in nathan_preferences and nathan_preferences[available_days[i]] =='monday':
                solver.add(day[i] == False)

    # Add constraints for meeting duration
    for i in range(len(available_days)):
        solver.add(end_time[i] == start_time[i] + meeting_duration)

    # Solve the problem
    if solver.check() == sat:
        model = solver.model()
        day_to_meet = [str(model.evaluate(day[i])).split(' ')[1] for i in range(len(available_days)) if model.evaluate(day[i])]
        start_time_to_meet = [str(model.evaluate(start_time[i])).split(' ')[1] for i in range(len(available_days)) if model.evaluate(day[i])]
        end_time_to_meet = [str(model.evaluate(end_time[i])).split(' ')[1] for i in range(len(available_days)) if model.evaluate(day[i])]
        return f'SOLUTION:\nDay: {day_to_meet[0]}\nStart Time: {start_time_to_meet[0]}\nEnd Time: {end_time_to_meet[0]}'
    else:
        return 'No solution found'

# Example usage
available_days = ['Monday', 'Tuesday']
amanda_schedule = [[9, 10.5], [11, 11.5], [12.5, 13], [13.5, 14], [14.5, 15], 
                   [9, 9.5], [10, 10.5], [11.5, 12], [13.5, 14.5], [15.5, 16], [16.5, 17]]
nathan_schedule = [[10, 10.5], [11, 11.5], [13.5, 14.5], [16, 16.5], 
                   [9, 10.5], [11, 13], [13.5, 14], [14.5, 15.5], [16, 16.5]]
meeting_duration = 0.5
amanda_preferences = {'Tuesday': 'after_11:00'}
nathan_preferences = {'Monday': True}

print(schedule_meeting(available_days, amanda_schedule, nathan_schedule, meeting_duration, amanda_preferences, nathan_preferences))