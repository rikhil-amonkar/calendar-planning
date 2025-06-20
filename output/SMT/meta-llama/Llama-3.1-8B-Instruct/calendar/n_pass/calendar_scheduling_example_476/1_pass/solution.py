from z3 import *

# Define the day of the week (Monday = 0, Tuesday = 1,..., Sunday = 6)
days = [0]

# Define the start and end times in minutes (9:00 = 0, 9:30 = 30,..., 17:00 = 480)
times = [i * 30 for i in range(17)]

# Define the meeting duration in minutes (30 minutes)
meeting_duration = 30

# Define the participants and their schedules
participants = {
    'Daniel': [],
    'Kathleen': [i * 30 + 450 for i in range(1, 5)],
    'Carolyn': [i * 30 + 360 for i in range(2)] + [i * 30 + 390 for i in range(2)],
    'Roger': [],
    'Cheryl': [i * 30 + 0 for i in range(3)] + [i * 30 + 300 for i in range(2)] + [i * 30 + 420 for i in range(4)],
    'Virginia': [i * 30 + 30 for i in range(3)] + [i * 30 + 360 for i in range(2)] + [i * 30 + 450 for i in range(2)] + [i * 30 + 480 for i in range(1)],
    'Angela': [i * 30 + 30 for i in range(1)] + [i * 30 + 210 for i in range(2)] + [i * 30 + 360 for i in range(2)] + [i * 30 + 420 for i in range(2)]
}

# Add Roger's preference
participants['Roger'] = [i * 30 + 420 for i in range(3)] + [i * 30 + 450 for i in range(2)]

# Define the solver
s = Solver()

# Define the variables
day = Int('day')
start_time = Int('start_time')
end_time = Int('end_time')

# Add constraints
s.add(day == 0)  # Monday
s.add(start_time >= 0)  # 9:00
s.add(end_time <= 480)  # 17:00
s.add(end_time - start_time == meeting_duration)  # 30 minutes
for participant in participants:
    s.add(start_time >= max(0, max(participants[participant]) + 1))
s.add(Or([start_time + meeting_duration > times for times in participants['Roger']]))

# Check if a solution exists
if s.check() == sat:
    model = s.model()
    print('SOLUTION:')
    print(f'Day: {days[model[day]]}')
    print(f'Start Time: {str(model[start_time]).zfill(2)}:00')
    print(f'End Time: {str(model[end_time]).zfill(2)}:00')
else:
    print('No solution exists')