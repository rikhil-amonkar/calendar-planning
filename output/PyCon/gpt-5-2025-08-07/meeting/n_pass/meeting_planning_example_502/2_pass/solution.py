import json
from datetime import datetime, timedelta

def time_to_minutes(time_str):
    """Convert time string (H:MM) to minutes since midnight"""
    dt = datetime.strptime(time_str, "%H:%M")
    return dt.hour * 60 + dt.minute

def minutes_to_time(minutes):
    """Convert minutes since midnight to time string (H:MM)"""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Travel times in minutes (from_location, to_location): time
    travel_times = {
        ('Financial District', 'Golden Gate Park'): 23,
        ('Financial District', 'Chinatown'): 5,
        ('Financial District', 'Union Square'): 9,
        ('Financial District', 'Fisherman\'s Wharf'): 10,
        ('Financial District', 'Pacific Heights'): 13,
        ('Financial District', 'North Beach'): 7,
        ('Golden Gate Park', 'Financial District'): 26,
        ('Golden Gate Park', 'Chinatown'): 23,
        ('Golden Gate Park', 'Union Square'): 22,
        ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
        ('Golden Gate Park', 'Pacific Heights'): 16,
        ('Golden Gate Park', 'North Beach'): 24,
        ('Chinatown', 'Financial District'): 5,
        ('Chinatown', 'Golden Gate Park'): 23,
        ('Chinatown', 'Union Square'): 7,
        ('Chinatown', 'Fisherman\'s Wharf'): 8,
        ('Chinatown', 'Pacific Heights'): 10,
        ('Chinatown', 'North Beach'): 3,
        ('Union Square', 'Financial District'): 9,
        ('Union Square', 'Golden Gate Park'): 22,
        ('Union Square', 'Chinatown'): 7,
        ('Union Square', 'Fisherman\'s Wharf'): 15,
        ('Union Square', 'Pacific Heights'): 15,
        ('Union Square', 'North Beach'): 10,
        ('Fisherman\'s Wharf', 'Financial District'): 11,
        ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
        ('Fisherman\'s Wharf', 'Chinatown'): 12,
        ('Fisherman\'s Wharf', 'Union Square'): 13,
        ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
        ('Fisherman\'s Wharf', 'North Beach'): 6,
        ('Pacific Heights', 'Financial District'): 13,
        ('Pacific Heights', 'Golden Gate Park'): 15,
        ('Pacific Heights', 'Chinatown'): 11,
        ('Pacific Heights', 'Union Square'): 12,
        ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
        ('Pacific Heights', 'North Beach'): 9,
        ('North Beach', 'Financial District'): 8,
        ('North Beach', 'Golden Gate Park'): 22,
        ('North Beach', 'Chinatown'): 6,
        ('North Beach', 'Union Square'): 7,
        ('North Beach', 'Fisherman\'s Wharf'): 5,
        ('North Beach', 'Pacific Heights'): 8
    }
    
    # Friend constraints
    friends = {
        'Stephanie': {
            'location': 'Golden Gate Park',
            'available_start': time_to_minutes('11:00'),
            'available_end': time_to_minutes('15:00'),
            'min_duration': 105
        },
        'Karen': {
            'location': 'Chinatown',
            'available_start': time_to_minutes('13:45'),
            'available_end': time_to_minutes('16:30'),
            'min_duration': 15
        },
        'Brian': {
            'location': 'Union Square',
            'available_start': time_to_minutes('15:00'),
            'available_end': time_to_minutes('17:15'),
            'min_duration': 30
        },
        'Rebecca': {
            'location': 'Fisherman\'s Wharf',
            'available_start': time_to_minutes('8:00'),
            'available_end': time_to_minutes('11:15'),
            'min_duration': 30
        },
        'Joseph': {
            'location': 'Pacific Heights',
            'available_start': time_to_minutes('8:15'),
            'available_end': time_to_minutes('9:30'),
            'min_duration': 60
        },
        'Steven': {
            'location': 'North Beach',
            'available_start': time_to_minutes('14:30'),
            'available_end': time_to_minutes('20:45'),
            'min_duration': 120
        }
    }
    
    # Start at Financial District at 9:00 AM
    current_time = time_to_minutes('9:00')
    current_location = 'Financial District'
    
    itinerary = []
    
    # Create a list of friends we can potentially meet
    available_friends = []
    for name, info in friends.items():
        # Check if friend is available after our start time
        earliest_possible_start = max(info['available_start'], current_time)
        if earliest_possible_start + info['min_duration'] <= info['available_end']:
            available_friends.append({
                'name': name,
                'location': info['location'],
                'available_start': info['available_start'],
                'available_end': info['available_end'],
                'min_duration': info['min_duration'],
                'earliest_possible_start': earliest_possible_start
            })
    
    # Sort friends by their earliest possible start time
    available_friends.sort(key=lambda x: x['earliest_possible_start'])
    
    # Greedy algorithm: try to meet friends in order of earliest availability
    for friend in available_friends:
        # Calculate travel time from current location
        travel_time = travel_times.get((current_location, friend['location']), 60)
        
        # Calculate when we would arrive
        arrival_time = current_time + travel_time
        
        # Determine the actual start time for the meeting
        # It must be after we arrive AND during the friend's availability
        actual_start = max(arrival_time, friend['available_start'])
        
        # Check if we can complete the meeting within the friend's availability
        if actual_start + friend['min_duration'] <= friend['available_end']:
            # Schedule the meeting
            end_time = actual_start + friend['min_duration']
            
            itinerary.append({
                "action": "meet",
                "location": friend['location'],
                "person": friend['name'],
                "start_time": minutes_to_time(actual_start),
                "end_time": minutes_to_time(end_time)
            })
            
            # Update current time and location
            current_time = end_time
            current_location = friend['location']
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()