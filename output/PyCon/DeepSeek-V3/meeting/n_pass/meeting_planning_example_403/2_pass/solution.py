import json
from datetime import datetime, timedelta

def time_to_minutes(time_str):
    """Convert time string (H:MM) to minutes since midnight"""
    if isinstance(time_str, str):
        dt = datetime.strptime(time_str, '%H:%M')
    else:
        dt = time_str
    return dt.hour * 60 + dt.minute

def minutes_to_time(minutes):
    """Convert minutes since midnight to time string (H:MM)"""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Travel times in minutes (symmetric matrix)
    travel_times = {
        'Union Square': {
            'Union Square': 0, 'Golden Gate Park': 22, 'Pacific Heights': 15, 
            'Presidio': 24, 'Chinatown': 7, 'The Castro': 19
        },
        'Golden Gate Park': {
            'Union Square': 22, 'Golden Gate Park': 0, 'Pacific Heights': 16, 
            'Presidio': 11, 'Chinatown': 23, 'The Castro': 13
        },
        'Pacific Heights': {
            'Union Square': 12, 'Golden Gate Park': 15, 'Pacific Heights': 0, 
            'Presidio': 11, 'Chinatown': 11, 'The Castro': 16
        },
        'Presidio': {
            'Union Square': 22, 'Golden Gate Park': 12, 'Pacific Heights': 11, 
            'Presidio': 0, 'Chinatown': 21, 'The Castro': 21
        },
        'Chinatown': {
            'Union Square': 7, 'Golden Gate Park': 23, 'Pacific Heights': 10, 
            'Presidio': 19, 'Chinatown': 0, 'The Castro': 22
        },
        'The Castro': {
            'Union Square': 19, 'Golden Gate Park': 11, 'Pacific Heights': 16, 
            'Presidio': 20, 'Chinatown': 20, 'The Castro': 0
        }
    }
    
    # Friend constraints
    friends = {
        'Andrew': {
            'location': 'Golden Gate Park',
            'available_start': time_to_minutes('11:45'),
            'available_end': time_to_minutes('14:30'),
            'min_duration': 75
        },
        'Sarah': {
            'location': 'Pacific Heights',
            'available_start': time_to_minutes('16:15'),
            'available_end': time_to_minutes('18:45'),
            'min_duration': 15
        },
        'Nancy': {
            'location': 'Presidio',
            'available_start': time_to_minutes('17:30'),
            'available_end': time_to_minutes('19:15'),
            'min_duration': 60
        },
        'Rebecca': {
            'location': 'Chinatown',
            'available_start': time_to_minutes('9:45'),
            'available_end': time_to_minutes('21:30'),
            'min_duration': 90
        },
        'Robert': {
            'location': 'The Castro',
            'available_start': time_to_minutes('8:30'),
            'available_end': time_to_minutes('14:15'),
            'min_duration': 30
        }
    }
    
    # Start at Union Square at 9:00 AM
    current_time = time_to_minutes('9:00')
    current_location = 'Union Square'
    
    itinerary = []
    visited_friends = set()
    
    # Try to schedule meetings in a greedy manner
    # We'll try multiple passes with different strategies
    
    # Strategy 1: Try to meet friends in chronological order of their availability windows
    friends_by_availability = sorted(friends.items(), key=lambda x: x[1]['available_start'])
    
    for friend_name, friend_info in friends_by_availability:
        if friend_name in visited_friends:
            continue
            
        location = friend_info['location']
        available_start = friend_info['available_start']
        available_end = friend_info['available_end']
        min_duration = friend_info['min_duration']
        
        # Calculate travel time from current location
        travel_time = travel_times[current_location][location]
        
        # Earliest we can start this meeting
        earliest_start = max(current_time + travel_time, available_start)
        
        # Check if we can fit this meeting
        if earliest_start + min_duration <= available_end:
            # Schedule the meeting
            start_time = earliest_start
            end_time = start_time + min_duration
            
            itinerary.append({
                'action': 'meet',
                'location': location,
                'person': friend_name,
                'start_time': minutes_to_time(start_time),
                'end_time': minutes_to_time(end_time)
            })
            
            visited_friends.add(friend_name)
            current_time = end_time
            current_location = location
    
    # Strategy 2: Try to fill gaps with friends we haven't visited yet
    # Sort remaining friends by location proximity to current location
    remaining_friends = [f for f in friends if f not in visited_friends]
    
    if remaining_friends:
        # Sort by travel time from current location
        remaining_friends.sort(key=lambda f: travel_times[current_location][friends[f]['location']])
        
        for friend_name in remaining_friends:
            friend_info = friends[friend_name]
            location = friend_info['location']
            available_start = friend_info['available_start']
            available_end = friend_info['available_end']
            min_duration = friend_info['min_duration']
            
            # Calculate travel time from current location
            travel_time = travel_times[current_location][location]
            
            # Earliest we can start this meeting
            earliest_start = max(current_time + travel_time, available_start)
            
            # Check if we can fit this meeting
            if earliest_start + min_duration <= available_end:
                # Schedule the meeting
                start_time = earliest_start
                end_time = start_time + min_duration
                
                itinerary.append({
                    'action': 'meet',
                    'location': location,
                    'person': friend_name,
                    'start_time': minutes_to_time(start_time),
                    'end_time': minutes_to_time(end_time)
                })
                
                visited_friends.add(friend_name)
                current_time = end_time
                current_location = location
    
    # Strategy 3: Try to optimize by reordering to fit more friends
    # This is a simplified approach - in a real scenario you might use more sophisticated algorithms
    
    result = {'itinerary': itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()