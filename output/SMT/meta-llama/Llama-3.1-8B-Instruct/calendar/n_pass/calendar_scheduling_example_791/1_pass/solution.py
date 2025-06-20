from z3 import *

def schedule_meeting(nicole_schedule, ruth_schedule, meeting_duration, preferred_days, ruth_preference):
    # Define the days of the week
    days = ['Monday', 'Tuesday', 'Wednesday']

    # Create a Z3 solver
    s = Solver()

    # Define the variables
    day = [Bool(f'day_{i}') for i in range(len(days))]
    start_time = [Int(f'start_time_{i}') for i in range(len(days))]
    end_time = [Int(f'end_time_{i}') for i in range(len(days))]

    # Add constraints for each day
    for i, d in enumerate(days):
        # Nicole is not available at the start time
        s.add(Or([start_time[i] < nicole_schedule[d][0] for d in days if nicole_schedule[d]]))
        # Nicole is not available at the end time
        s.add(Or([end_time[i] > nicole_schedule[d][-1] for d in days if nicole_schedule[d]]))
        # Ruth is not available at the start time
        s.add(Or([start_time[i] < ruth_schedule[d][0] for d in days if ruth_schedule[d]]))
        # Ruth is not available at the end time
        s.add(Or([end_time[i] > ruth_schedule[d][-1] for d in days if ruth_schedule[d]]))
        # Ruth does not want to meet on Wednesday after 13:30 if it's Wednesday
        if d == 'Wednesday':
            s.add(Or([start_time[i] >= 13*60 + 30, end_time[i] < 17*60]))
        # The meeting duration is half an hour
        s.add(start_time[i] % 60 == 0)
        s.add(end_time[i] == start_time[i] + 30)
        # The start time is before the end time
        s.add(start_time[i] < end_time[i])
        # The day is preferred if it's in the preferred days
        s.add(day[i] == preferred_days[d] if d in preferred_days else day[i] == False)

    # Add a constraint to select one day
    s.add(Or(day))

    # Add a constraint to check if the meeting time is available for both participants
    s.add(And([start_time[i] >= nicole_schedule[d][0] for d in days if nicole_schedule[d] and day[i]]))
    s.add(And([start_time[i] >= ruth_schedule[d][0] for d in days if ruth_schedule[d] and day[i]]))
    s.add(And([end_time[i] <= nicole_schedule[d][-1] for d in days if nicole_schedule[d] and day[i]]))
    s.add(And([end_time[i] <= ruth_schedule[d][-1] for d in days if ruth_schedule[d] and day[i]]))

    # Add a constraint to check if Ruth's preference is met
    s.add(If(day[2], And([start_time[2] >= 13*60 + 30, end_time[2] < 17*60]), True))

    # Solve the problem
    if s.check() == sat:
        # Get the model
        m = s.model()
        # Print the solution
        day_index = [i for i, d in enumerate(day) if m[d].as_bool().value()]
        solution = f'SOLUTION:\nDay: {days[day_index[0]]}\nStart Time: {m[start_time[day_index[0]]].as_int():02d}:{m[start_time[day_index[0]]].as_int() % 60:02d}\nEnd Time: {m[end_time[day_index[0]]].as_int():02d}:{m[end_time[day_index[0]]].as_int() % 60:02d}'
    else:
        solution = 'No solution found'

    return solution

# Define the existing schedules
nicole_schedule = {
    'Monday': [9*60, 9*60 + 30, 13*60, 13*60 + 30, 14*60 + 30, 15*60],
    'Tuesday': [9*60, 9*60 + 30, 11*60 + 30, 13*60, 14*60 + 30, 15*60],
    'Wednesday': [10*60, 11*60, 12*60 + 30, 15*60, 16*60, 17*60]
}

ruth_schedule = {
    'Monday': [9*60, 17*60],
    'Tuesday': [9*60, 17*60],
    'Wednesday': [9*60, 10*60 + 30, 11*60, 11*60 + 30, 12*60, 12*60 + 30, 13*60 + 30, 15*60, 16*60, 16*60 + 30]
}

# Define the meeting duration
meeting_duration = 30

# Define the preferred days
preferred_days = {
    'Monday': True,
    'Tuesday': True,
    'Wednesday': True
}

# Define Ruth's preference
ruth_preference = {
    'Wednesday': True
}

# Print the solution
print(schedule_meeting(nicole_schedule, ruth_schedule, meeting_duration, preferred_days, ruth_preference))