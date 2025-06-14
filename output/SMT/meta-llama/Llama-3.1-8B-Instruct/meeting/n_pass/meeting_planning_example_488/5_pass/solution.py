YOUR_CODE
from z3 import *

# Define the variables
start_time = 0
end_time = 24 * 60  # 24 hours in minutes
locations = ['Pacific Heights', 'Nob Hill', 'Russian Hill', 'The Castro', 'Sunset District', 'Haight-Ashbury']
travel_times = {
    'Pacific Heights': {'Nob Hill': 8, 'Russian Hill': 7, 'The Castro': 16, 'Sunset District': 21, 'Haight-Ashbury': 11},
    'Nob Hill': {'Pacific Heights': 8, 'Russian Hill': 5, 'The Castro': 17, 'Sunset District': 25, 'Haight-Ashbury': 13},
    'Russian Hill': {'Pacific Heights': 7, 'Nob Hill': 5, 'The Castro': 21, 'Sunset District': 23, 'Haight-Ashbury': 17},
    'The Castro': {'Pacific Heights': 16, 'Nob Hill': 16, 'Russian Hill': 18, 'Sunset District': 17, 'Haight-Ashbury': 6},
    'Sunset District': {'Pacific Heights': 21, 'Nob Hill': 27, 'Russian Hill': 24, 'The Castro': 17, 'Haight-Ashbury': 15},
    'Haight-Ashbury': {'Pacific Heights': 12, 'Nob Hill': 15, 'Russian Hill': 17, 'The Castro': 6, 'Sunset District': 15}
}
meetings = {
    'Ronald': {'location': 'Nob Hill','start_time': 10 * 60, 'end_time': 17 * 60,'min_time': 105},
    'Sarah': {'location': 'Russian Hill','start_time': 0, 'end_time': 9 * 60,'min_time': 45},
    'Helen': {'location': 'The Castro','start_time': 1 * 60, 'end_time': 17 * 60,'min_time': 120},
    'Joshua': {'location': 'Sunset District','start_time': 2 * 60, 'end_time': 22 * 60,'min_time': 90},
    'Margaret': {'location': 'Haight-Ashbury','start_time': 10 * 60, 'end_time': 24 * 60,'min_time': 60}
}

# Create the solver
solver = Solver()

# Create the variables
times = [Int('t_' + str(i)) for i in range(len(locations) + 1)]
locations_at_time = [Int('l_' + str(i)) for i in range(len(locations) + 1)]
meetings_satisfied = [Bool('m_' + str(i)) for i in range(len(meetings))]

# Add the constraints
for i in range(len(locations) + 1):
    solver.add(0 <= times[i])
    solver.add(times[i] <= end_time)
    solver.add(locations_at_time[i] >= 0)
    solver.add(locations_at_time[i] <= len(locations))

for i in range(len(locations)):
    solver.add(locations_at_time[i] == locations_at_time[i + 1])

for i in range(len(locations)):
    for j in range(len(locations)):
        if i!= j:
            solver.add(times[i + 1] >= times[i] + travel_times[locations[i]][locations[j]])

for i, meeting in enumerate(meetings.values()):
    start_location = locations.index('Pacific Heights')
    end_location = locations.index(meeting['location'])
    solver.add(If(locations_at_time[start_location] == 0, 
                 And(times[start_location + 1] >= meeting['start_time'], 
                     times[len(locations)] - travel_times[meeting['location']]['Pacific Heights'] <= meeting['end_time'], 
                     times[start_location + 1] + travel_times[meeting['location']]['Pacific Heights'] + meeting['min_time'] <= times[len(locations)] - travel_times[meeting['location']]['Pacific Heights']), 
                 meetings_satisfied[i]))

# Add the objective function
objective = 0
for i in range(len(meetings)):
    objective += If(meetings_satisfied[i], meeting['min_time'], 0)

# Solve the problem
solver.add(And([locations_at_time[0] == 0]))
solver.minimize(objective)
result = solver.check()

if result == sat:
    model = solver.model()
    print('SOLUTION:')
    for i in range(len(meetings)):
        print(f'Meeting with {list(meetings.keys())[i]} at {model[times[0]].as_long()}:{model[times[len(locations)] - travel_times[meetings[list(meetings.keys())[i]]["location"]]["Pacific Heights"]].as_long()}')
else:
    print('No solution found')