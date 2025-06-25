from z3 import *

def schedule_meeting(participants, meeting_duration, preferences=None):
    # Create a Z3 solver
    solver = Solver()

    # Define the day and time variables
    day = [Bool(f'day_{i}') for i in range(1)]
    time = [Int(f'time_{i}') for i in range(24*60)]
    for i in range(24*60):
        time[i] = If(day[0], Int('time'), 0)

    # Define the constraints for the day
    solver.add(Or(day[0]))

    # Define the constraints for the time
    for i in range(24*60):
        solver.add(And(9 * 60 <= i, i <= 17 * 60))

    # Define the constraints for the participants
    for participant, schedule in participants.items():
        for time_slot in schedule:
            start, end = time_slot
            for i in range(24*60):
                solver.add(If(day[0], And(start * 60 <= i, i <= end * 60), True))

    # Define the constraints for the meeting duration
    for i in range(24*60):
        start_time = i
        end_time = start_time + meeting_duration * 60
        solver.add(And(9 * 60 <= start_time, start_time <= 17 * 60))
        solver.add(And(start_time <= end_time, end_time <= 17 * 60))

    # Define the constraints for the preferences
    if preferences:
        for participant, time in preferences.items():
            if participant in participants:
                solver.add(If(day[0], Not(Int(time * 60) <= Int(0)), True))

    # Solve the constraints
    if solver.check() == sat:
        model = solver.model()
        day = model.evaluate(day[0]).as_long()
        start_time = model.evaluate(time[0]).as_long()
        end_time = start_time + meeting_duration * 60
        return f'SOLUTION:\nDay: {["Monday"][0]}\nStart Time: {start_time // 60:02d}:{start_time % 60:02d}\nEnd Time: {end_time // 60:02d}:{end_time % 60:02d}'
    else:
        return 'No solution found'

# Define the participants and their schedules
participants = {
    'Jose': [(11, 11.5), (12.5, 13)],
    'Keith': [(14, 14.5), (15, 15.5)],
    'Logan': [(9, 10), (12, 12.5), (15, 15.5)],
    'Megan': [(9, 10.5), (11, 12), (13, 13.5), (14.5, 16.5)],
    'Gary': [(9, 9.5), (10, 10.5), (11.5, 13), (13.5, 14), (14.5, 16.5)],
    'Bobby': [(11, 11.5), (12, 12.5), (13, 16)]
}

# Define the meeting duration and preferences
meeting_duration = 0.5
preferences = {
    'Jose': 15.5
}

# Print the solution
print(schedule_meeting(participants, meeting_duration, preferences))