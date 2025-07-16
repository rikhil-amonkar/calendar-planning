import json
from itertools import permutations

# Travel times in minutes between locations
travel_times = {
    'Golden Gate Park': {
        'Golden Gate Park': 0,
        'Alcatraz': 45,
        'Fisherman\'s Wharf': 30,
        'Union Square': 35,
        'Chinatown': 40,
        'Lombard Street': 25,
        'Coit Tower': 30,
        'Pier 39': 35
    },
    'Alcatraz': {
        'Golden Gate Park': 45,
        'Alcatraz': 0,
        'Fisherman\'s Wharf': 10,
        'Union Square': 25,
        'Chinatown': 20,
        'Lombard Street': 15,
        'Coit Tower': 10,
        'Pier 39': 15
    },
    'Fisherman\'s Wharf': {
        'Golden Gate Park': 30,
        'Alcatraz': 10,
        'Fisherman\'s Wharf': 0,
        'Union Square': 15,
        'Chinatown': 10,
        'Lombard Street': 5,
        'Coit Tower': 5,
        'Pier 39': 5
    },
    'Union Square': {
        'Golden Gate Park': 35,
        'Alcatraz': 25,
        'Fisherman\'s Wharf': 15,
        'Union Square': 0,
        'Chinatown': 5,
        'Lombard Street': 10,
        'Coit Tower': 15,
        'Pier 39': 20
    },
    'Chinatown': {
        'Golden Gate Park': 40,
        'Alcatraz': 20,
        'Fisherman\'s Wharf': 10,
        'Union Square': 5,
        'Chinatown': 0,
        'Lombard Street': 8,
        'Coit Tower': 10,
        'Pier 39': 15
    },
    'Lombard Street': {
        'Golden Gate Park': 25,
        'Alcatraz': 15,
        'Fisherman\'s Wharf': 5,
        'Union Square': 10,
        'Chinatown': 8,
        'Lombard Street': 0,
        'Coit Tower': 5,
        'Pier 39': 10
    },
    'Coit Tower': {
        'Golden Gate Park': 30,
        'Alcatraz': 10,
        'Fisherman\'s Wharf': 5,
        'Union Square': 15,
        'Chinatown': 10,
        'Lombard Street': 5,
        'Coit Tower': 0,
        'Pier 39': 10
    },
    'Pier 39': {
        'Golden Gate Park': 35,
        'Alcatraz': 15,
        'Fisherman\'s Wharf': 5,
        'Union Square': 20,
        'Chinatown': 15,
        'Lombard Street': 10,
        'Coit Tower': 10,
        'Pier 39': 0
    }
}

# Friend information
friends = [
    {'name': 'Alice', 'location': 'Fisherman\'s Wharf', 'available_start': 9.5, 'available_end': 15.0, 'duration': 60},
    {'name': 'Bob', 'location': 'Alcatraz', 'available_start': 10.0, 'available_end': 16.0, 'duration': 30},
    {'name': 'Charlie', 'location': 'Union Square', 'available_start': 10.0, 'available_end': 14.0, 'duration': 45},
    {'name': 'Dana', 'location': 'Chinatown', 'available_start': 11.0, 'available_end': 16.0, 'duration': 30},
    {'name': 'Eve', 'location': 'Lombard Street', 'available_start': 9.5, 'available_end': 12.0, 'duration': 30},
    {'name': 'Frank', 'location': 'Coit Tower', 'available_start': 11.0, 'available_end': 14.0, 'duration': 45},
    {'name': 'Grace', 'location': 'Pier 39', 'available_start': 10.0, 'available_end': 13.0, 'duration': 30}
]

def time_to_float(time_str):
    if isinstance(time_str, str):
        hours, minutes = map(int, time_str.split(':'))
        return hours + minutes / 60.0
    return time_str  # already a float

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
        
        # Calculate travel time from current location (convert to hours)
        travel_time = travel_times[current_location].get(location, float('inf')) / 60.0
        
        # Arrival time at friend's location
        arrival_time = current_time + travel_time
        
        # Calculate meeting window
        start_time = max(arrival_time, time_to_float(friend['available_start']))
        end_time = start_time + friend['duration'] / 60.0
        
        # Check if meeting fits in friend's availability
        if end_time > time_to_float(friend['available_end']):
            return None
        
        # Add to itinerary
        itinerary.append({
            'action': 'meet',
            'location': location,
            'person': friend['name'],
            'start_time': float_to_time(start_time),
            'end_time': float_to_time(end_time)
        })
        
        # Update current location and time
        current_location = location
        current_time = end_time
    
    return itinerary

def evaluate_schedule(itinerary):
    if not itinerary:
        return -1  # invalid schedule
    # Prioritize more friends met, then earlier finish time
    return len(itinerary) * 100 - time_to_float(itinerary[-1]['end_time'])

def find_optimal_schedule():
    best_score = -1
    best_itinerary = []
    
    # Try all possible orders of different lengths (from 7 down to 1)
    for num_friends in range(len(friends), 0, -1):
        for order in permutations(range(len(friends)), num_friends):
            itinerary = calculate_schedule(order)
            if itinerary is None:
                continue
            score = evaluate_schedule(itinerary)
            if score > best_score:
                best_score = score
                best_itinerary = itinerary
                # Early exit if we found a schedule meeting all friends
                if len(best_itinerary) == len(friends):
                    return best_itinerary
    
    return best_itinerary if best_score != -1 else []

def main():
    optimal_itinerary = find_optimal_schedule()
    result = {
        "itinerary": optimal_itinerary
    }
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()