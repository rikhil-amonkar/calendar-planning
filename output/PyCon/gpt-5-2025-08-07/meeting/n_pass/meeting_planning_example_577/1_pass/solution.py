import constraint
from datetime import datetime, timedelta
import json

def time_to_minutes(time_str):
    """Convert time string (H:MM) to minutes since midnight"""
    dt = datetime.strptime(time_str, '%H:%M')
    return dt.hour * 60 + dt.minute

def minutes_to_time(minutes):
    """Convert minutes since midnight to time string (H:MM)"""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Travel times matrix (in minutes)
    travel_times = {
        ('Haight-Ashbury', 'Russian Hill'): 17,
        ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23,
        ('Haight-Ashbury', 'Nob Hill'): 15,
        ('Haight-Ashbury', 'Golden Gate Park'): 7,
        ('Haight-Ashbury', 'Alamo Square'): 5,
        ('Haight-Ashbury', 'Pacific Heights'): 12,
        ('Russian Hill', 'Haight-Ashbury'): 17,
        ('Russian Hill', 'Fisherman\'s Wharf'): 7,
        ('Russian Hill', 'Nob Hill'): 5,
        ('Russian Hill', 'Golden Gate Park'): 21,
        ('Russian Hill', 'Alamo Square'): 15,
        ('Russian Hill', 'Pacific Heights'): 7,
        ('Fisherman\'s Wharf', 'Haight-Ashbury'): 22,
        ('Fisherman\'s Wharf', 'Russian Hill'): 7,
        ('Fisherman\'s Wharf', 'Nob Hill'): 11,
        ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
        ('Fisherman\'s Wharf', 'Alamo Square'): 20,
        ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
        ('Nob Hill', 'Haight-Ashbury'): 13,
        ('Nob Hill', 'Russian Hill'): 5,
        ('Nob Hill', 'Fisherman\'s Wharf'): 11,
        ('Nob Hill', 'Golden Gate Park'): 17,
        ('Nob Hill', 'Alamo Square'): 11,
        ('Nob Hill', 'Pacific Heights'): 8,
        ('Golden Gate Park', 'Haight-Ashbury'): 7,
        ('Golden Gate Park', 'Russian Hill'): 19,
        ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
        ('Golden Gate Park', 'Nob Hill'): 20,
        ('Golden Gate Park', 'Alamo Square'): 10,
        ('Golden Gate Park', 'Pacific Heights'): 16,
        ('Alamo Square', 'Haight-Ashbury'): 5,
        ('Alamo Square', 'Russian Hill'): 13,
        ('Alamo Square', 'Fisherman\'s Wharf'): 19,
        ('Alamo Square', 'Nob Hill'): 11,
        ('Alamo Square', 'Golden Gate Park'): 9,
        ('Alamo Square', 'Pacific Heights'): 10,
        ('Pacific Heights', 'Haight-Ashbury'): 11,
        ('Pacific Heights', 'Russian Hill'): 7,
        ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
        ('Pacific Heights', 'Nob Hill'): 8,
        ('Pacific Heights', 'Golden Gate Park'): 15,
        ('Pacific Heights', 'Alamo Square'): 10,
    }
    
    # Friend constraints
    friends = [
        {
            'name': 'Stephanie',
            'location': 'Russian Hill',
            'available_start': '20:00',
            'available_end': '20:45',
            'min_duration': 15
        },
        {
            'name': 'Kevin',
            'location': 'Fisherman\'s Wharf',
            'available_start': '19:15',
            'available_end': '21:45',
            'min_duration': 75
        },
        {
            'name': 'Robert',
            'location': 'Nob Hill',
            'available_start': '7:45',
            'available_end': '10:30',
            'min_duration': 90
        },
        {
            'name': 'Steven',
            'location': 'Golden Gate Park',
            'available_start': '8:30',
            'available_end': '17:00',
            'min_duration': 75
        },
        {
            'name': 'Anthony',
            'location': 'Alamo Square',
            'available_start': '7:45',
            'available_end': '19:45',
            'min_duration': 15
        },
        {
            'name': 'Sandra',
            'location': 'Pacific Heights',
            'available_start': '14:45',
            'available_end': '21:45',
            'min_duration': 45
        }
    ]
    
    # Start time at Haight-Ashbury
    start_time_minutes = time_to_minutes('9:00')
    current_time = start_time_minutes
    current_location = 'Haight-Ashbury'
    
    itinerary = []
    
    # Try to meet friends in order of their availability and constraints
    # Sort friends by their available start time
    sorted_friends = sorted(friends, key=lambda x: time_to_minutes(x['available_start']))
    
    for friend in sorted_friends:
        # Calculate travel time to friend's location
        travel_time = travel_times.get((current_location, friend['location']), 0)
        
        # Arrival time at friend's location
        arrival_time = current_time + travel_time
        
        # Friend's available window
        friend_start = time_to_minutes(friend['available_start'])
        friend_end = time_to_minutes(friend['available_end'])
        
        # Check if we can meet this friend
        if arrival_time <= friend_end:
            # Start meeting as soon as possible after arrival
            meeting_start = max(arrival_time, friend_start)
            
            # Calculate meeting end time
            meeting_end = meeting_start + friend['min_duration']
            
            # Ensure meeting doesn't exceed friend's availability
            if meeting_end <= friend_end:
                # Add meeting to itinerary
                itinerary.append({
                    "action": "meet",
                    "location": friend['location'],
                    "person": friend['name'],
                    "start_time": minutes_to_time(meeting_start),
                    "end_time": minutes_to_time(meeting_end)
                })
                
                # Update current time and location
                current_time = meeting_end
                current_location = friend['location']
    
    # Output result
    result = {
        "itinerary": itinerary
    }
    
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()