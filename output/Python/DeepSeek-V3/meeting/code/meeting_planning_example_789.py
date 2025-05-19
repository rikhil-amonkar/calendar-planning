import json
from itertools import permutations

# Travel times dictionary (from -> to -> minutes)
travel_times = {
    'Union Square': {
        'Russian Hill': 13,
        'Alamo Square': 15,
        'Haight-Ashbury': 18,
        'Marina District': 18,
        'Bayview': 15,
        'Chinatown': 7,
        'Presidio': 24,
        'Sunset District': 27
    },
    'Russian Hill': {
        'Union Square': 10,
        'Alamo Square': 15,
        'Haight-Ashbury': 17,
        'Marina District': 7,
        'Bayview': 23,
        'Chinatown': 9,
        'Presidio': 14,
        'Sunset District': 23
    },
    'Alamo Square': {
        'Union Square': 14,
        'Russian Hill': 13,
        'Haight-Ashbury': 5,
        'Marina District': 15,
        'Bayview': 16,
        'Chinatown': 15,
        'Presidio': 17,
        'Sunset District': 16
    },
    'Haight-Ashbury': {
        'Union Square': 19,
        'Russian Hill': 17,
        'Alamo Square': 5,
        'Marina District': 17,
        'Bayview': 18,
        'Chinatown': 19,
        'Presidio': 15,
        'Sunset District': 15
    },
    'Marina District': {
        'Union Square': 16,
        'Russian Hill': 8,
        'Alamo Square': 15,
        'Haight-Ashbury': 16,
        'Bayview': 27,
        'Chinatown': 15,
        'Presidio': 10,
        'Sunset District': 19
    },
    'Bayview': {
        'Union Square': 18,
        'Russian Hill': 23,
        'Alamo Square': 16,
        'Haight-Ashbury': 19,
        'Marina District': 27,
        'Chinatown': 19,
        'Presidio': 32,
        'Sunset District': 23
    },
    'Chinatown': {
        'Union Square': 7,
        'Russian Hill': 7,
        'Alamo Square': 17,
        'Haight-Ashbury': 19,
        'Marina District': 12,
        'Bayview': 20,
        'Presidio': 19,
        'Sunset District': 29
    },
    'Presidio': {
        'Union Square': 22,
        'Russian Hill': 14,
        'Alamo Square': 19,
        'Haight-Ashbury': 15,
        'Marina District': 11,
        'Bayview': 31,
        'Chinatown': 21,
        'Sunset District': 16
    },
    'Sunset District': {
        'Union Square': 30,
        'Russian Hill': 24,
        'Alamo Square': 17,
        'Haight-Ashbury': 15,
        'Marina District': 21,
        'Bayview': 22,
        'Chinatown': 30,
        'Presidio': 16
    }
}

# Friend data: name, location, available_start, available_end, min_duration (in minutes)
friends = [
    ('Betty', 'Russian Hill', 7*60, 16*60+45, 105),
    ('Melissa', 'Alamo Square', 9*60+30, 17*60+15, 105),
    ('Joshua', 'Haight-Ashbury', 12*60+15, 19*60, 90),
    ('Jeffrey', 'Marina District', 12*60+15, 18*60, 45),
    ('James', 'Bayview', 7*60+30, 20*60, 90),
    ('Anthony', 'Chinatown', 11*60+45, 13*60+30, 75),
    ('Timothy', 'Presidio', 12*60+30, 14*60+45, 90),
    ('Emily', 'Sunset District', 19*60+30, 21*60+30, 120)
]

def time_to_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def evaluate_schedule(order):
    current_time = 9 * 60  # Start at Union Square at 9:00 AM
    current_location = 'Union Square'
    schedule = []
    met_friends = set()
    
    for friend_idx in order:
        name, loc, avail_start, avail_end, min_dur = friends[friend_idx]
        
        # Calculate travel time
        travel_time = travel_times[current_location].get(loc, float('inf'))
        if travel_time == float('inf'):
            return None, 0
        
        arrival_time = current_time + travel_time
        start_time = max(arrival_time, avail_start)
        end_time = start_time + min_dur
        
        if end_time > avail_end:
            return None, 0
        
        schedule.append({
            'action': 'meet',
            'location': loc,
            'person': name,
            'start_time': time_to_str(start_time),
            'end_time': time_to_str(end_time)
        })
        
        met_friends.add(friend_idx)
        current_time = end_time
        current_location = loc
    
    # Check if we can meet Emily in Sunset District at the end
    travel_time = travel_times[current_location].get('Sunset District', float('inf'))
    if travel_time == float('inf'):
        return None, len(met_friends)
    
    arrival_time = current_time + travel_time
    emily = friends[-1]  # Emily is last in the list
    start_time = max(arrival_time, emily[2])
    end_time = start_time + emily[4]
    
    if end_time <= emily[3]:
        schedule.append({
            'action': 'meet',
            'location': 'Sunset District',
            'person': 'Emily',
            'start_time': time_to_str(start_time),
            'end_time': time_to_str(end_time)
        })
        met_friends.add(len(friends)-1)
    
    return schedule, len(met_friends)

def find_optimal_schedule():
    best_schedule = None
    best_count = 0
    
    # We'll try permutations of friend indices (excluding Emily who must be last)
    friend_indices = list(range(len(friends)-1))
    
    # Try all possible orders (but limit to 10000 permutations for performance)
    for perm in permutations(friend_indices):
        schedule, count = evaluate_schedule(perm)
        if count > best_count or (count == best_count and schedule is not None):
            best_schedule = schedule
            best_count = count
            if best_count == len(friends):  # Can't do better than meeting everyone
                break
    
    return best_schedule

def main():
    optimal_schedule = find_optimal_schedule()
    result = {
        "itinerary": optimal_schedule if optimal_schedule else []
    }
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()