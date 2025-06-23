from z3 import *

# Define the travel distances
travel_distances = {
    'Presidio': {'Haight-Ashbury': 15, 'Nob Hill': 18, 'Russian Hill': 14, 'North Beach': 18, 'Chinatown': 21, 'Union Square': 22, 'Embarcadero': 20, 'Financial District': 23, 'Marina District': 11},
    'Haight-Ashbury': {'Presidio': 15, 'Nob Hill': 15, 'Russian Hill': 17, 'North Beach': 19, 'Chinatown': 19, 'Union Square': 19, 'Embarcadero': 20, 'Financial District': 21, 'Marina District': 17},
    'Nob Hill': {'Presidio': 18, 'Haight-Ashbury': 15, 'Russian Hill': 5, 'North Beach': 8, 'Chinatown': 6, 'Union Square': 7, 'Embarcadero': 9, 'Financial District': 9, 'Marina District': 11},
    'Russian Hill': {'Presidio': 14, 'Haight-Ashbury': 17, 'Nob Hill': 5, 'North Beach': 5, 'Chinatown': 9, 'Union Square': 10, 'Embarcadero': 8, 'Financial District': 11, 'Marina District': 7},
    'North Beach': {'Presidio': 18, 'Haight-Ashbury': 19, 'Nob Hill': 7, 'Russian Hill': 4, 'Chinatown': 6, 'Union Square': 7, 'Embarcadero': 6, 'Financial District': 8, 'Marina District': 9},
    'Chinatown': {'Presidio': 21, 'Haight-Ashbury': 19, 'Nob Hill': 9, 'Russian Hill': 7, 'North Beach': 3, 'Union Square': 7, 'Embarcadero': 5, 'Financial District': 5, 'Marina District': 12},
    'Union Square': {'Presidio': 22, 'Haight-Ashbury': 18, 'Nob Hill': 9, 'Russian Hill': 13, 'North Beach': 10, 'Chinatown': 7, 'Embarcadero': 11, 'Financial District': 9, 'Marina District': 18},
    'Embarcadero': {'Presidio': 20, 'Haight-Ashbury': 21, 'Nob Hill': 10, 'Russian Hill': 8, 'North Beach': 5, 'Chinatown': 7, 'Union Square': 10, 'Financial District': 5, 'Marina District': 12},
    'Financial District': {'Presidio': 23, 'Haight-Ashbury': 19, 'Nob Hill': 8, 'Russian Hill': 11, 'North Beach': 7, 'Chinatown': 5, 'Union Square': 9, 'Embarcadero': 4, 'Marina District': 15},
    'Marina District': {'Presidio': 11, 'Haight-Ashbury': 16, 'Nob Hill': 12, 'Russian Hill': 8, 'North Beach': 11, 'Chinatown': 15, 'Union Square': 16, 'Embarcadero': 14, 'Financial District': 17}
}

# Define the constraints
start_time = 9 * 60  # 9:00 AM
end_time = 21 * 60  # 9:00 PM

friends = {
    'Karen': {'location': 'Haight-Ashbury','start_time': 9 * 60, 'end_time': 9 * 60 + 45 * 60, 'duration': 45 * 60},
    'Jessica': {'location': 'Nob Hill','start_time': 1 * 60 + 45 * 60, 'end_time': 21 * 60, 'duration': 90 * 60},
    'Brian': {'location': 'Russian Hill','start_time': 3 * 60 + 30 * 60, 'end_time': 21 * 60, 'duration': 60 * 60},
    'Kenneth': {'location': 'North Beach','start_time': 9 * 60, 'end_time': 21 * 60, 'duration': 30 * 60},
    'Jason': {'location': 'Chinatown','start_time': 8 * 60 + 15 * 60, 'end_time': 11 * 60 + 45 * 60, 'duration': 75 * 60},
    'Stephanie': {'location': 'Union Square','start_time': 2 * 60 + 45 * 60, 'end_time': 18 * 60 + 45 * 60, 'duration': 105 * 60},
    'Kimberly': {'location': 'Embarcadero','start_time': 9 * 60, 'end_time': 19 * 60 + 30 * 60, 'duration': 75 * 60},
    'Steven': {'location': 'Financial District','start_time': 7 * 60 + 15 * 60, 'end_time': 21 * 60, 'duration': 60 * 60},
    'Mark': {'location': 'Marina District','start_time': 10 * 60 + 15 * 60, 'end_time': 13 * 60 + 0 * 60, 'duration': 75 * 60}
}

# Create the Z3 solver
s = Solver()

# Define the variables
locations = list(travel_distances.keys())
times = [start_time + i * 60 for i in range(int((end_time - start_time) / 60) + 1)]
location_at_time = {location: [Bool(f'{location}_at_{time}') for time in times] for location in locations}
visited_location = {location: [Bool(f'versited_{location}_at_{time}') for time in times] for location in locations}
time_location = {time: [Bool(f'time_location_{time}_{location}') for location in locations] for time in times}

# Add the constraints
for location in locations:
    s.add(Or([visited_location[location][i] for i in range(len(times))]))

for friend in friends.values():
    location = friend['location']
    start_time = friend['start_time']
    end_time = friend['end_time']
    duration = friend['duration']
    for time in times:
        if start_time <= time <= end_time:
            s.add(visited_location[location][time // 60])

# Add the distance constraints
for location1 in locations:
    for location2 in locations:
        if location1!= location2:
            for time in times:
                if time > 0:
                    distance = travel_distances[location1][location2]
                    s.add(If(visited_location[location1][time // 60], visited_location[location2][time // 60 + distance], False))

# Add the time_location constraints
for time in times:
    for location in locations:
        s.add(time_location[time][location] == visited_location[location][time // 60])

# Add the one location at a time constraints
for time in times:
    s.add(Or([time_location[time][location] for location in locations]).eq(1))

# Solve the problem
s.check()
model = s.model()

# Print the solution
solution = {}
for location in locations:
    location_at_time_list = [model[visited_location[location][i]].as_bool() for i in range(len(times))]
    location_at_time_list = [time for time, visited in zip(times, location_at_time_list) if visited]
    solution[location] = location_at_time_list

# Print the final answer
print('SOLUTION:')
for location, times in solution.items():
    print(f'{location}: {times}')