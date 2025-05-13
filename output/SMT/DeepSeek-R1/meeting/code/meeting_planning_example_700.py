from z3 import *

# Define friends data with their constraints
friends = [
    {
        'name': 'Michelle',
        'location': 'Golden Gate Park',
        'start_available': 20 * 60,
        'end_available': 21 * 60,
        'duration': 15,
        'travel_time_from_presidio': 12
    },
    {
        'name': 'Emily',
        'location': 'Fisherman\'s Wharf',
        'start_available': 16 * 60 + 15,
        'end_available': 19 * 60,
        'duration': 30,
        'travel_time_from_presidio': 19
    },
    {
        'name': 'Mark',
        'location': 'Marina District',
        'start_available': 18 * 60 + 15,
        'end_available': 19 * 60 + 45,
        'duration': 75,
        'travel_time_from_presidio': 11
    },
    {
        'name': 'Barbara',
        'location': 'Alamo Square',
        'start_available': 17 * 60,
        'end_available': 19 * 60,
        'duration': 120,
        'travel_time_from_presidio': 19
    },
    {
        'name': 'Laura',
        'location': 'Sunset District',
        'start_available': 19 * 60,
        'end_available': 21 * 60 + 15,
        'duration': 75,
        'travel_time_from_presidio': 15
    },
    {
        'name': 'Mary',
        'location': 'Nob Hill',
        'start_available': 17 * 60 + 30,
        'end_available': 19 * 60,
        'duration': 45,
        'travel_time_from_presidio': 18
    },
    {
        'name': 'Helen',
        'location': 'North Beach',
        'start_available': 11 * 60,
        'end_available': 12 * 60 + 15,
        'duration': 45,
        'travel_time_from_presidio': 18
    }
]

# Define travel times between all locations
travel_times = {
    'Presidio': {
        'Pacific Heights': 11,
        'Golden Gate Park': 12,
        'Fisherman\'s Wharf': 19,
        'Marina District': 11,
        'Alamo Square': 19,
        'Sunset District': 15,
        'Nob Hill': 18,
        'North Beach': 18,
    },
    'Pacific Heights': {
        'Presidio': 11,
        'Golden Gate Park': 15,
        'Fisherman\'s Wharf': 13,
        'Marina District': 6,
        'Alamo Square': 10,
        'Sunset District': 21,
        'Nob Hill': 8,
        'North Beach': 9,
    },
    'Golden Gate Park': {
        'Presidio': 12,
        'Pacific Heights': 16,
        'Fisherman\'s Wharf': 24,
        'Marina District': 16,
        'Alamo Square': 9,
        'Sunset District': 10,
        'Nob Hill': 20,
        'North Beach': 23,
    },
    'Fisherman\'s Wharf': {
        'Presidio': 19,
        'Pacific Heights': 12,
        'Golden Gate Park': 25,
        'Marina District': 9,
        'Alamo Square': 21,
        'Sunset District': 27,
        'Nob Hill': 11,
        'North Beach': 6,
    },
    'Marina District': {
        'Presidio': 11,
        'Pacific Heights': 7,
        'Golden Gate Park': 18,
        'Fisherman\'s Wharf': 10,
        'Alamo Square': 15,
        'Sunset District': 19,
        'Nob Hill': 12,
        'North Beach': 11,
    },
    'Alamo Square': {
        'Presidio': 19,
        'Pacific Heights': 10,
        'Golden Gate Park': 9,
        'Fisherman\'s Wharf': 19,
        'Marina District': 15,
        'Sunset District': 16,
        'Nob Hill': 11,
        'North Beach': 15,
    },
    'Sunset District': {
        'Presidio': 15,
        'Pacific Heights': 21,
        'Golden Gate Park': 11,
        'Fisherman\'s Wharf': 29,
        'Marina District': 21,
        'Alamo Square': 17,
        'Nob Hill': 27,
        'North Beach': 28,
    },
    'Nob Hill': {
        'Presidio': 18,
        'Pacific Heights': 8,
        'Golden Gate Park': 17,
        'Fisherman\'s Wharf': 10,
        'Marina District': 11,
        'Alamo Square': 11,
        'Sunset District': 24,
        'North Beach': 8,
    },
    'North Beach': {
        'Presidio': 18,
        'Pacific Heights': 9,
        'Golden Gate Park': 23,
        'Fisherman\'s Wharf': 5,
        'Marina District': 9,
        'Alamo Square': 16,
        'Sunset District': 28,
        'Nob Hill': 7,
    },
}

# Initialize Z3 solver and optimize
s = Optimize()

# Create variables for each friend
for friend in friends:
    friend['visited'] = Bool(f'visited_{friend["name"]}')
    friend['start'] = Int(f'start_{friend["name"]}')
    friend['end'] = Int(f'end_{friend["name"]}')

# Add constraints for each friend
for friend in friends:
    s.add(Implies(friend['visited'],
                  And(friend['start'] >= friend['start_available'],
                      friend['end'] == friend['start'] + friend['duration'],
                      friend['end'] <= friend['end_available'],
                      friend['start'] >= 540 + friend['travel_time_from_presidio'])))

# Add pairwise constraints for travel times
for i in range(len(friends)):
    for j in range(i + 1, len(friends)):
        friend_i = friends[i]
        friend_j = friends[j]
        loc_i = friend_i['location']
        loc_j = friend_j['location']
        travel_ij = travel_times[loc_i][loc_j]
        travel_ji = travel_times[loc_j][loc_i]
        s.add(Implies(And(friend_i['visited'], friend_j['visited']),
                      Or(friend_j['start'] >= friend_i['end'] + travel_ij,
                         friend_i['start'] >= friend_j['end'] + travel_ji)))

# Maximize the number of visited friends
sum_visited = Sum([If(friend['visited'], 1, 0) for friend in friends])
s.maximize(sum_visited)

# Check and print the solution
if s.check() == sat:
    model = s.model()
    print("Optimal schedule:")
    for friend in friends:
        if model.evaluate(friend['visited']):
            start = model.evaluate(friend['start'])
            end = model.evaluate(friend['end'])
            start_hr = start.as_long() // 60
            start_min = start.as_long() % 60
            end_hr = end.as_long() // 60
            end_min = end.as_long() % 60
            print(f"{friend['name']}: {start_hr:02d}:{start_min:02d} to {end_hr:02d}:{end_min:02d}")
else:
    print("No solution found.")