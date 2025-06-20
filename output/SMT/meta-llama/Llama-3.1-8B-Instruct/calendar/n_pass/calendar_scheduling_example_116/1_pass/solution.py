from z3 import *

def schedule_meeting(day, start_time, end_time, participants, constraints, preferences=None):
    # Create a Z3 solver
    solver = Solver()

    # Define the variables
    times = []
    for participant in participants:
        times.append([Bool(f'{participant}_{time}') for time in range(int(start_time), int(end_time))])

    # Add the constraints
    for participant in participants:
        for i, time in enumerate(times[participants.index(participant)]):
            if i < int(start_time.split(':')[0])*60 + int(start_time.split(':')[1]) or i >= int(end_time.split(':')[0])*60 + int(end_time.split(':')[1]):
                solver.add(Not(time))  # Time is out of bounds
            elif f'{participant}_{constraints[participants.index(participant)]}' == str(i):
                solver.add(Not(time))  # Time is busy

    # Add the constraints for each participant
    for participant in participants:
        solver.add(Or([times[participants.index(participant)][i] for i in range(int(start_time), int(end_time))]))

    # Add the preference constraints if any
    if preferences is not None:
        for participant, pref in preferences.items():
            for i, time in enumerate(times[participants.index(participant)]):
                if i < int(pref.split(':')[0])*60 + int(pref.split(':')[1]) or i >= int(end_time.split(':')[0])*60 + int(end_time.split(':')[1]):
                    solver.add(Not(time))  # Time is out of bounds
                elif f'{participant}_{pref}' == str(i):
                    solver.add(Not(time))  # Time is preferred

    # Check if there's a solution
    if solver.check() == sat:
        model = solver.model()
        start_time_str = ''
        end_time_str = ''
        for time in times[0]:
            if model.evaluate(time).as_bool():
                start_time_str = str(int(start_time.split(':')[0])) + ':' + str(int(start_time.split(':')[1]))
                end_time_str = str(int(end_time.split(':')[0])) + ':' + str(int(end_time.split(':')[1]))
                break

        return f'Day: {day}\nStart Time: {start_time_str}\nEnd Time: {end_time_str}'
    else:
        return 'No solution found'

# Define the participants, constraints, and preferences
participants = ['Adam', 'John', 'Stephanie', 'Anna']
constraints = {
    'Adam': '14:00',
    'John': '13:00,14:00,15:30,16:30',
    'Stephanie': '9:30,10:30,11:30,16:30',
    'Anna': '9:30,12:00,13:00,16:30'
}
preferences = {
    'Anna': '14:30'
}

# Define the day, start time, and end time
day = 'Monday'
start_time = '9:00'
end_time = '17:00'

# Call the function to schedule the meeting
print(schedule_meeting(day, start_time, end_time, participants, constraints, preferences))