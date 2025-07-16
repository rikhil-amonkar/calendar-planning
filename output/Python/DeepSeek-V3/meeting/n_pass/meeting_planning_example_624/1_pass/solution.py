import json
from itertools import permutations

# Travel times dictionary
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

# Friend constraints
friends = [
    {
        'name': 'Carol',
        'location': 'Haight-Ashbury',
        'available_start': 21.5,  # 9:30 PM
        'available_end': 22.5,    # 10:30 PM
        'duration': 60            # minutes
    },
    {
        'name': 'Laura',
        'location': 'Fisherman\'s Wharf',
        'available_start': 11.75, # 11:45 AM
        'available_end': 21.5,   # 9:30 PM
        'duration': 60
    },
    {
        'name': 'Karen',
        'location': 'The Castro',
        'available_start': 7.25,  # 7:15 AM
        'available_end': 14.0,   # 2:00 PM
        'duration': 75
    },
    {
        'name': 'Elizabeth',
        'location': 'Chinatown',
        'available_start': 12.25, # 12:15 PM
        'available_end': 21.5,   # 9:30 PM
        'duration': 75
    },
    {
        'name': 'Deborah',
        'location': 'Alamo Square',
        'available_start': 12.0,  # 12:00 PM
        'available_end': 15.0,    # 3:00 PM
        'duration': 105
    },
    {
        'name': 'Jason',
        'location': 'North Beach',
        'available_start': 14.75, # 2:45 PM
        'available_end': 19.0,     # 7:00 PM
        'duration': 90
    },
    {
        'name': 'Steven',
        'location': 'Russian Hill',
        'available_start': 14.75,  # 2:45 PM
        'available_end': 18.5,    # 6:30 PM
        'duration': 120
    }
]

def time_to_float(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours + minutes / 60.0

def float_to_time(time_float):
    hours = int(time_float)
    minutes = int((time_float - hours) * 60)
    return f"{hours}:{minutes:02d}"

def calculate_schedule(order):
    current_location = 'Golden Gate Park'
    current_time = 9.0  # 9:00 AM
    itinerary = []
    
    for friend_idx in order:
        friend = friends[friend_idx]
        location = friend['location']
        travel_time = travel_times[current_location].get(location, float('inf'))
        
        # Arrival time at friend's location
        arrival_time = current_time + travel_time / 60.0
        
        # Calculate meeting window
        start_time = max(arrival_time, friend['available_start'])
        end_time = start_time + friend['duration'] / 60.0
        
        if end_time > friend['available_end']:
            return None  # Doesn't fit
        
        itinerary.append({
            'action': 'meet',
            'location': location,
            'person': friend['name'],
            'start_time': float_to_time(start_time),
            'end_time': float_to_time(end_time)
        })
        
        current_location = location
        current_time = end_time
    
    return itinerary

def evaluate_schedule(itinerary):
    if not itinerary:
        return 0
    # Count number of friends met
    return len(itinerary)

def find_optimal_schedule():
    best_score = 0
    best_itinerary = []
    
    # Try all possible orders (limited to 5 friends due to computational constraints)
    for order in permutations(range(len(friends)), 5):
        itinerary = calculate_schedule(order)
        score = evaluate_schedule(itinerary)
        if score > best_score:
            best_score = score
            best_itinerary = itinerary
    
    return best_itinerary

def main():
    optimal_itinerary = find_optimal_schedule()
    result = {
        "itinerary": optimal_itinerary
    }
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()