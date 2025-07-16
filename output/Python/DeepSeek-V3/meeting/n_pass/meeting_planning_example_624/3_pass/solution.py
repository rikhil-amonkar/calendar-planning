import json
from itertools import permutations

# (Travel times dictionary remains the same)
travel_times = {
    # ... (same as original)
}

# (Friend constraints remain the same)
friends = [
    # ... (same as original)
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
        
        # Calculate travel time from current location
        travel_time = travel_times[current_location].get(location, float('inf')) / 60.0
        
        # Arrival time at friend's location
        arrival_time = current_time + travel_time
        
        # Calculate meeting window
        start_time = max(arrival_time, friend['available_start'])
        end_time = start_time + friend['duration'] / 60.0
        
        # Check if meeting fits in friend's availability
        if end_time > friend['available_end']:
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
        return 0
    # Prioritize more friends met, then earlier finish time
    return len(itinerary) - (time_to_float(itinerary[-1]['end_time']) / 24.0)

def find_optimal_schedule():
    best_score = -1
    best_itinerary = []
    
    # Try all possible orders of different lengths (from 7 down to 1)
    for num_friends in range(len(friends), 0, -1):
        for order in permutations(range(len(friends)), num_friends):
            itinerary = calculate_schedule(order)
            score = evaluate_schedule(itinerary)
            if score > best_score:
                best_score = score
                best_itinerary = itinerary
                # Early exit if we found a schedule meeting all friends
                if len(best_itinerary) == len(friends):
                    return best_itinerary
    
    return best_itinerary

def main():
    optimal_itinerary = find_optimal_schedule()
    result = {
        "itinerary": optimal_itinerary
    }
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()