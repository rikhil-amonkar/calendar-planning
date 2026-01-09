import json
from datetime import datetime, timedelta

def main():
    # Define locations
    locations = ['Bayview', 'Nob Hill', 'Union Square', 'Chinatown', 'The Castro', 'Presidio', 'Pacific Heights', 'Russian Hill']
    
    # Travel times matrix (in minutes)
    travel_times = {
        'Bayview': {'Bayview': 0, 'Nob Hill': 20, 'Union Square': 17, 'Chinatown': 18, 'The Castro': 20, 'Presidio': 31, 'Pacific Heights': 23, 'Russian Hill': 23},
        'Nob Hill': {'Bayview': 19, 'Nob Hill': 0, 'Union Square': 7, 'Chinatown': 6, 'The Castro': 17, 'Presidio': 17, 'Pacific Heights': 8, 'Russian Hill': 5},
        'Union Square': {'Bayview': 15, 'Nob Hill': 9, 'Union Square': 0, 'Chinatown': 7, 'The Castro': 19, 'Presidio': 24, 'Pacific Heights': 15, 'Russian Hill': 13},
        'Chinatown': {'Bayview': 22, 'Nob Hill': 8, 'Union Square': 7, 'Chinatown': 0, 'The Castro': 22, 'Presidio': 19, 'Pacific Heights': 10, 'Russian Hill': 7},
        'The Castro': {'Bayview': 19, 'Nob Hill': 16, 'Union Square': 19, 'Chinatown': 20, 'The Castro': 0, 'Presidio': 20, 'Pacific Heights': 16, 'Russian Hill': 18},
        'Presidio': {'Bayview': 31, 'Nob Hill': 18, 'Union Square': 22, 'Chinatown': 21, 'The Castro': 21, 'Presidio': 0, 'Pacific Heights': 11, 'Russian Hill': 14},
        'Pacific Heights': {'Bayview': 22, 'Nob Hill': 8, 'Union Square': 12, 'Chinatown': 11, 'The Castro': 16, 'Presidio': 11, 'Pacific Heights': 0, 'Russian Hill': 7},
        'Russian Hill': {'Bayview': 23, 'Nob Hill': 5, 'Union Square': 11, 'Chinatown': 9, 'The Castro': 21, 'Presidio': 14, 'Pacific Heights': 7, 'Russian Hill': 0}
    }
    
    # Friend constraints
    friends = [
        {'name': 'Paul', 'location': 'Nob Hill', 'available_start': '16:15', 'available_end': '21:15', 'min_duration': 60},
        {'name': 'Carol', 'location': 'Union Square', 'available_start': '18:00', 'available_end': '20:15', 'min_duration': 120},
        {'name': 'Patricia', 'location': 'Chinatown', 'available_start': '20:00', 'available_end': '21:30', 'min_duration': 75},
        {'name': 'Karen', 'location': 'The Castro', 'available_start': '17:00', 'available_end': '19:00', 'min_duration': 45},
        {'name': 'Nancy', 'location': 'Presidio', 'available_start': '11:45', 'available_end': '22:00', 'min_duration': 30},
        {'name': 'Jeffrey', 'location': 'Pacific Heights', 'available_start': '20:00', 'available_end': '20:45', 'min_duration': 45},
        {'name': 'Matthew', 'location': 'Russian Hill', 'available_start': '15:45', 'available_end': '21:45', 'min_duration': 75}
    ]
    
    # Convert time strings to minutes since 9:00
    def time_to_minutes(time_str):
        if ':' in time_str:
            hours, minutes = map(int, time_str.split(':'))
            return (hours - 9) * 60 + minutes
        return 0
    
    def minutes_to_time(minutes):
        total_hours = 9 + minutes // 60
        total_minutes = minutes % 60
        return f"{total_hours}:{total_minutes:02d}"
    
    # Sort friends by available start time to try to meet them in order
    friends_sorted = sorted(friends, key=lambda x: time_to_minutes(x['available_start']))
    
    # Build itinerary using greedy approach
    itinerary = []
    current_location = 'Bayview'
    current_time = time_to_minutes('9:00')
    
    # Track which friends we've met
    met_friends = set()
    
    # Try to meet as many friends as possible
    while len(met_friends) < len(friends_sorted):
        best_next_friend = None
        best_start_time = None
        best_end_time = None
        best_travel_time = float('inf')
        
        for friend in friends_sorted:
            if friend['name'] in met_friends:
                continue
                
            location = friend['location']
            available_start = time_to_minutes(friend['available_start'])
            available_end = time_to_minutes(friend['available_end'])
            min_duration = friend['min_duration']
            
            # Calculate travel time
            travel_time = travel_times[current_location][location]
            
            # Calculate earliest possible start time
            earliest_arrival = current_time + travel_time
            actual_start = max(earliest_arrival, available_start)
            
            # Check if meeting is possible
            if actual_start + min_duration <= available_end:
                # Calculate total time including travel
                total_time = travel_time + min_duration
                
                # Prefer friends with less travel time and earlier availability
                if (best_next_friend is None or 
                    travel_time < best_travel_time or
                    (travel_time == best_travel_time and actual_start < best_start_time)):
                    
                    best_next_friend = friend
                    best_start_time = actual_start
                    best_end_time = actual_start + min_duration
                    best_travel_time = travel_time
        
        if best_next_friend is None:
            # No more friends can be met
            break
        
        # Add travel to itinerary if we're moving to a new location
        if current_location != best_next_friend['location']:
            itinerary.append({
                'action': 'travel',
                'from': current_location,
                'to': best_next_friend['location'],
                'start_time': minutes_to_time(current_time),
                'end_time': minutes_to_time(current_time + best_travel_time)
            })
        
        # Add meeting to itinerary
        itinerary.append({
            'action': 'meet',
            'location': best_next_friend['location'],
            'person': best_next_friend['name'],
            'start_time': minutes_to_time(best_start_time),
            'end_time': minutes_to_time(best_end_time)
        })
        
        # Update current state
        current_location = best_next_friend['location']
        current_time = best_end_time
        met_friends.add(best_next_friend['name'])
    
    # If we couldn't meet all friends, try to meet remaining ones with adjusted schedule
    if len(met_friends) < len(friends_sorted):
        remaining_friends = [f for f in friends_sorted if f['name'] not in met_friends]
        
        for friend in remaining_friends:
            location = friend['location']
            available_start = time_to_minutes(friend['available_start'])
            available_end = time_to_minutes(friend['available_end'])
            min_duration = friend['min_duration']
            
            travel_time = travel_times[current_location][location]
            earliest_arrival = current_time + travel_time
            actual_start = max(earliest_arrival, available_start)
            
            if actual_start + min_duration <= available_end:
                # Add travel
                if current_location != location:
                    itinerary.append({
                        'action': 'travel',
                        'from': current_location,
                        'to': location,
                        'start_time': minutes_to_time(current_time),
                        'end_time': minutes_to_time(current_time + travel_time)
                    })
                
                # Add meeting
                itinerary.append({
                    'action': 'meet',
                    'location': location,
                    'person': friend['name'],
                    'start_time': minutes_to_time(actual_start),
                    'end_time': minutes_to_time(actual_start + min_duration)
                })
                
                current_location = location
                current_time = actual_start + min_duration
                met_friends.add(friend['name'])
    
    # Filter itinerary to only include meet actions as requested
    meet_itinerary = [item for item in itinerary if item['action'] == 'meet']
    
    result = {'itinerary': meet_itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()