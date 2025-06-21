from z3 import *

# Define the day and time slots
day = 'Monday'
start_time = 9
end_time = 17
time_slots = [str(i) + ':00' for i in range(start_time, end_time + 1)]
time_slots += [str(i) + ':30' for i in range(start_time, end_time + 1) if i % 2 == 1]

# Define the participants and their constraints
participants = ['Margaret', 'Donna', 'Helen']
constraints = {
    'Margaret': ['09:00', '10:00', '10:30', '11:00', '11:30', '12:00', '13:00', '13:30', '15:00', '15:30'],
    'Donna': ['14:30', '16:00', '16:30'],
    'Helen': ['09:00', '09:30', '10:00', '10:30', '11:30', '13:00', '14:00', '14:30', '15:00', '15:30', '17:00']
}

# Define the meeting duration and Helen's preference
meeting_duration = 30
helen_preference = '13:30'

# Create Z3 solver
s = Solver()

# Declare the variables
day_var = Bool('day')
time_var = Int('time')

# Add constraints for the day
s.add(day_var == (day == 'Monday'))

# Add constraints for the time
time_slots_var = [Int(f'time_{i}') for i in range(len(time_slots))]
for i in range(len(time_slots_var)):
    s.add(Or([time_slots_var[i] == int(time_slots[i].split(':')[0])]))
s.add(And([time_slots_var[i] <= time_slots_var[i + 1] for i in range(len(time_slots_var) - 1)]))

# Add constraints for the participants
for participant in participants:
    participant_constraints = [Int(f'{participant}_{i}') for i in range(len(constraints[participant]))]
    for i in range(len(participant_constraints)):
        s.add(Or([participant_constraints[i] == int(constraints[participant][i].split(':')[0])]))
    s.add(And([participant_constraints[i] <= participant_constraints[i + 1] for i in range(len(participant_constraints) - 1)]))

# Add constraints for the meeting duration
s.add(time_var + meeting_duration >= time_var)

# Add constraints for Helen's preference
helen_constraints = [Int(f'Helen_{i}') for i in range(len(constraints['Helen']))]
for i in range(len(helen_constraints)):
    s.add(Or([helen_constraints[i] == int(constraints['Helen'][i].split(':')[0])]))
s.add(And([helen_constraints[i] <= helen_constraints[i + 1] for i in range(len(helen_constraints) - 1)]))
s.add(Or([helen_constraints[i] >= int(helen_preference.split(':')[0]) for i in range(len(helen_constraints))]))

# Add constraints for the meeting time
s.add(And([time_var >= start_time, time_var <= end_time]))

# Solve the constraints
s.add(Implies(day_var, And([time_var + meeting_duration <= end_time, time_var >= start_time])))
s.add(Implies(day_var, Not(Or([time_var >= int(constraints[participant][i].split(':')[0]) for participant in participants for i in range(len(constraints[participant]))]))))
s.add(Implies(day_var, Not(Or([time_var + meeting_duration >= int(constraints[participant][i].split(':')[0]) for participant in participants for i in range(len(constraints[participant]))]))))

if s.check() == sat:
    m = s.model()
    print('SOLUTION:')
    print(f'Day: {day}')
    print(f'Start Time: {m[time_var].as_string()}')
    print(f'End Time: {str(int(m[time_var].as_string()) + meeting_duration).zfill(2) + ":00"}")
else:
    print('No solution found')