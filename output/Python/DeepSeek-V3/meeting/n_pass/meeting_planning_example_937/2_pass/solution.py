import json
from datetime import datetime, timedelta

def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# (Existing travel_times and friends dictionaries remain the same)

def get_travel_time(from_loc, to_loc):
    if from_loc == to_loc:
        return 0
    return travel_times[from_loc][to_loc]

def generate_itinerary():
    itinerary = []
    current_time = time_to_minutes('9:00')
    current_location = 'Russian Hill'
    
    # Create a list of friends sorted by their end time (earlier first)
    sorted_friends = sorted(friends.items(), key=lambda x: time_to_minutes(x[1]['end']))
    
    visited = set()
    
    while len(visited) < len(friends):
        best_friend = None
        best_time = None
        best_start = None
        
        for name, data in sorted_friends:
            if name in visited:
                continue
                
            location = data['location']
            travel_time = get_travel_time(current_location, location)
            arrival_time = current_time + travel_time
            
            # Calculate possible meeting window
            window_start = max(arrival_time, time_to_minutes(data['start']))
            window_end = min(window_start + data['duration'], time_to_minutes(data['end']))
            
            # Check if we can complete the visit
            if window_end - window_start >= data['duration']:
                # Prefer friends with tighter schedules first
                if best_friend is None or (time_to_minutes(data['end']) < time_to_minutes(friends[best_friend]['end'])):
                    best_friend = name
                    best_time = travel_time
                    best_start = window_start
        
        if best_friend is None:
            break  # No more valid visits possible
            
        # Add to itinerary
        friend_data = friends[best_friend]
        end_time = best_start + friend_data['duration']
        
        itinerary.append({
            'action': 'meet',
            'location': friend_data['location'],
            'person': best_friend,
            'start_time': minutes_to_time(best_start),
            'end_time': minutes_to_time(end_time)
        })
        
        visited.add(best_friend)
        current_location = friend_data['location']
        current_time = end_time
    
    return itinerary

def main():
    itinerary = generate_itinerary()
    print(json.dumps({'itinerary': itinerary}, indent=2))

if __name__ == '__main__':
    main()