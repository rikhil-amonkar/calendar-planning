import itertools
import json

def minutes_to_time(minutes):
    hours = minutes // 60
    minutes_remainder = minutes % 60
    return f"{hours}:{minutes_remainder:02d}"

# Define travel times
travel_times = {
    'Golden Gate Park': {
        'Haight-Ashbury': 7,
        'Fisherman\'s Wharf': 24,
        'The Castro': 13,
        'Chinatown': 23,
        'Alamo Square': 10,
        'North Beach': 24,
        'Russian Hill': 19
    },
    'Haight-Ashbury': {
        'Golden Gate Park': 7,
        'Fisherman\'s Wharf': 23,
        'The Castro': 6,
        'Chinatown': 19,
        'Alamo Square': 5,
        'North Beach': 19,
        'Russian Hill': 17
    },
    'Fisherman\'s Wharf': {
        'Golden Gate Park': 25,
        'Haight-Ashbury': 22,
        'The Castro': 26,
        'Chinatown': 12,
        'Alamo Square': 20,
        'North Beach': 6,
        'Russian Hill': 7
    },
    'The Castro': {
        'Golden Gate Park': 11,
        'Haight-Ashbury': 6,
        'Fisherman\'s Wharf': 24,
        'Chinatown': 20,
        'Alamo Square': 8,
        'North Beach': 20,
        'Russian Hill': 18
    },
    'Chinatown': {
        'Golden Gate Park': 23,
        'Haight-Ashbury': 19,
        'Fisherman\'s Wharf': 8,
        'The Castro': 22,
        'Alamo Square': 17,
        'North Beach': 3,
        'Russian Hill': 7
    },
    'Alamo Square': {
        'Golden Gate Park': 9,
        'Haight-Ashbury': 5,
        'Fisherman\'s Wharf': 19,
        'The Castro': 8,
        'Chinatown': 16,
        'North Beach': 15,
        'Russian Hill': 13
    },
    'North Beach': {
        'Golden Gate Park': 22,
        'Haight-Ashbury': 18,
        'Fisherman\'s Wharf': 5,
        'The Castro': 22,
        'Chinatown': 6,
        'Alamo Square': 16,
        'Russian Hill': 4
    },
    'Russian Hill': {
        'Golden Gate Park': 21,
        'Haight-Ashbury': 17,
        'Fisherman\'s Wharf': 7,
        'The Castro': 21,
        'Chinatown': 9,
        'Alamo Square': 15,
        'North Beach': 5
    }
}

# Define friends with their constraints (times converted to minutes)
friends = [
    {'name': 'Carol', 'location': 'Haight-Ashbury', 'start': 21*60+30, 'end': 22*60+30, 'min_time': 60},
    {'name': 'Laura', 'location': 'Fisherman\'s Wharf', 'start': 11*60+45, 'end': 21*60+30, 'min_time': 60},
    {'name': 'Karen', 'location': 'The Castro', 'start': 7*60+15, 'end': 14*60, 'min_time': 75},
    {'name': 'Elizabeth', 'location': 'Chinatown', 'start': 12*60+15, 'end': 21*60+30, 'min_time': 75},
    {'name': 'Deborah', 'location': 'Alamo Square', 'start': 12*60, 'end': 15*60, 'min_time': 105},
    {'name': 'Jason', 'location': 'North Beach', 'start': 14*60+45, 'end': 19*60, 'min_time': 90},
    {'name': 'Steven', 'location': 'Russian Hill', 'start': 14*60+45, 'end': 18*60+30, 'min_time': 120}
]

# Separate Carol from other friends
carol_friend = None
non_carol_friends = []
for f in friends:
    if f['name'] == 'Carol':
        carol_friend = f
    else:
        non_carol_friends.append(f)

# Function to simulate a schedule given a permutation
def simulate_schedule(permutation, travel_times):
    current_time = 9 * 60  # 9:00 AM in minutes
    current_location = 'Golden Gate Park'
    itinerary = []
    
    for friend in permutation:
        # Travel to the friend's location
        travel_duration = travel_times[current_location][friend['location']]
        current_time += travel_duration
        
        # Determine meeting start time (max of arrival and friend's availability start)
        start_meeting = max(current_time, friend['start'])
        end_meeting = start_meeting + friend['min_time']
        
        # Check if meeting can be scheduled within the friend's availability
        if end_meeting > friend['end']:
            return False, None  # Infeasible schedule
        
        # Add meeting to itinerary (in minutes for now)
        itinerary.append({
            'friend': friend,
            'start': start_meeting,
            'end': end_meeting
        })
        
        current_time = end_meeting
        current_location = friend['location']
    
    return True, itinerary

# Search for the optimal schedule (max number of meetings)
solution_found = False
result_itinerary = []

# Try from 7 meetings down to 0
for r in range(len(friends), 0, -1):
    # Generate all combinations of friends of size r
    all_friends = non_carol_friends + ([carol_friend] if carol_friend else [])
    for subset in itertools.combinations(all_friends, r):
        carol_in_subset = carol_friend in subset
        
        if carol_in_subset:
            # Remove Carol and generate permutations of the rest
            non_carol_subset = [f for f in subset if f != carol_friend]
            for perm in itertools.permutations(non_carol_subset):
                full_perm = list(perm) + [carol_friend]
                feasible, itinerary_minutes = simulate_schedule(full_perm, travel_times)
                if feasible:
                    result_itinerary = itinerary_minutes
                    solution_found = True
                    break
            if solution_found:
                break
        else:
            for perm in itertools.permutations(subset):
                feasible, itinerary_minutes = simulate_schedule(perm, travel_times)
                if feasible:
                    result_itinerary = itinerary_minutes
                    solution_found = True
                    break
            if solution_found:
                break
    
    if solution_found:
        break

# Convert the itinerary to the required output format
output_itinerary = []
for meeting in result_itinerary:
    friend = meeting['friend']
    output_itinerary.append({
        "action": "meet",
        "location": friend['location'],
        "person": friend['name'],
        "start_time": minutes_to_time(meeting['start']),
        "end_time": minutes_to_time(meeting['end'])
    })

# Output as JSON
result = {
    "itinerary": output_itinerary
}
print(json.dumps(result))