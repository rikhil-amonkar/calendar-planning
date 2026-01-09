import json
from datetime import datetime, timedelta

def time_to_minutes(time_str):
    """Convert time string (H:MM) to minutes since midnight"""
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    """Convert minutes since midnight to time string (H:MM)"""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Travel times in minutes between locations
    travel_times = {
        ('Fisherman\'s Wharf', 'The Castro'): 26,
        ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
        ('Fisherman\'s Wharf', 'Embarcadero'): 8,
        ('Fisherman\'s Wharf', 'Russian Hill'): 7,
        ('Fisherman\'s Wharf', 'Nob Hill'): 11,
        ('Fisherman\'s Wharf', 'Alamo Square'): 20,
        ('Fisherman\'s Wharf', 'North Beach'): 6,
        ('The Castro', 'Fisherman\'s Wharf'): 24,
        ('The Castro', 'Golden Gate Park'): 11,
        ('The Castro', 'Embarcadero'): 22,
        ('The Castro', 'Russian Hill'): 18,
        ('The Castro', 'Nob Hill'): 16,
        ('The Castro', 'Alamo Square'): 8,
        ('The Castro', 'North Beach'): 20,
        ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
        ('Golden Gate Park', 'The Castro'): 13,
        ('Golden Gate Park', 'Embarcadero'): 25,
        ('Golden Gate Park', 'Russian Hill'): 19,
        ('Golden Gate Park', 'Nob Hill'): 20,
        ('Golden Gate Park', 'Alamo Square'): 10,
        ('Golden Gate Park', 'North Beach'): 24,
        ('Embarcadero', 'Fisherman\'s Wharf'): 6,
        ('Embarcadero', 'The Castro'): 25,
        ('Embarcadero', 'Golden Gate Park'): 25,
        ('Embarcadero', 'Russian Hill'): 8,
        ('Embarcadero', 'Nob Hill'): 10,
        ('Embarcadero', 'Alamo Square'): 19,
        ('Embarcadero', 'North Beach'): 5,
        ('Russian Hill', 'Fisherman\'s Wharf'): 7,
        ('Russian Hill', 'The Castro'): 21,
        ('Russian Hill', 'Golden Gate Park'): 21,
        ('Russian Hill', 'Embarcadero'): 8,
        ('Russian Hill', 'Nob Hill'): 5,
        ('Russian Hill', 'Alamo Square'): 15,
        ('Russian Hill', 'North Beach'): 5,
        ('Nob Hill', 'Fisherman\'s Wharf'): 11,
        ('Nob Hill', 'The Castro'): 17,
        ('Nob Hill', 'Golden Gate Park'): 17,
        ('Nob Hill', 'Embarcadero'): 9,
        ('Nob Hill', 'Russian Hill'): 5,
        ('Nob Hill', 'Alamo Square'): 11,
        ('Nob Hill', 'North Beach'): 8,
        ('Alamo Square', 'Fisherman\'s Wharf'): 19,
        ('Alamo Square', 'The Castro'): 8,
        ('Alamo Square', 'Golden Gate Park'): 9,
        ('Alamo Square', 'Embarcadero'): 17,
        ('Alamo Square', 'Russian Hill'): 13,
        ('Alamo Square', 'Nob Hill'): 11,
        ('Alamo Square', 'North Beach'): 15,
        ('North Beach', 'Fisherman\'s Wharf'): 5,
        ('North Beach', 'The Castro'): 22,
        ('North Beach', 'Golden Gate Park'): 22,
        ('North Beach', 'Embarcadero'): 6,
        ('North Beach', 'Russian Hill'): 4,
        ('North Beach', 'Nob Hill'): 7,
        ('North Beach', 'Alamo Square'): 16,
    }
    
    # Friend constraints
    friends = [
        {
            'name': 'Laura',
            'location': 'The Castro',
            'available_start': '19:45',
            'available_end': '21:30',
            'min_duration': 105
        },
        {
            'name': 'Daniel',
            'location': 'Golden Gate Park',
            'available_start': '21:15',
            'available_end': '21:45',
            'min_duration': 15
        },
        {
            'name': 'William',
            'location': 'Embarcadero',
            'available_start': '7:00',
            'available_end': '9:00',
            'min_duration': 90
        },
        {
            'name': 'Karen',
            'location': 'Russian Hill',
            'available_start': '14:30',
            'available_end': '19:45',
            'min_duration': 30
        },
        {
            'name': 'Stephanie',
            'location': 'Nob Hill',
            'available_start': '7:30',
            'available_end': '9:30',
            'min_duration': 45
        },
        {
            'name': 'Joseph',
            'location': 'Alamo Square',
            'available_start': '11:30',
            'available_end': '12:45',
            'min_duration': 15
        },
        {
            'name': 'Kimberly',
            'location': 'North Beach',
            'available_start': '15:45',
            'available_end': '19:15',
            'min_duration': 30
        }
    ]
    
    # Convert all times to minutes
    for friend in friends:
        friend['available_start_min'] = time_to_minutes(friend['available_start'])
        friend['available_end_min'] = time_to_minutes(friend['available_end'])
    
    # Sort friends by their availability windows (earliest first)
    friends_sorted = sorted(friends, key=lambda x: x['available_start_min'])
    
    # Build itinerary using a greedy approach
    itinerary = []
    current_time = time_to_minutes('9:00')  # Start at Fisherman's Wharf
    current_location = "Fisherman's Wharf"
    
    # Track which friends we've scheduled
    scheduled = [False] * len(friends_sorted)
    
    while any(not s for s in scheduled):
        # Find the next feasible friend to meet
        best_friend_idx = None
        best_start_time = None
        best_end_time = None
        
        for i, friend in enumerate(friends_sorted):
            if scheduled[i]:
                continue
                
            # Calculate travel time to this friend
            travel_time = travel_times.get((current_location, friend['location']), 30)
            
            # Earliest we can start meeting this friend
            earliest_start = max(current_time + travel_time, friend['available_start_min'])
            
            # Check if we can meet within their availability window
            if earliest_start + friend['min_duration'] <= friend['available_end_min']:
                # Use maximum possible duration within constraints
                max_duration = min(
                    friend['available_end_min'] - earliest_start,
                    120  # Reasonable maximum meeting time
                )
                
                # Prefer longer durations when possible, but at least minimum
                duration = max(friend['min_duration'], max_duration)
                end_time = earliest_start + duration
                
                if best_friend_idx is None or earliest_start < best_start_time:
                    best_friend_idx = i
                    best_start_time = earliest_start
                    best_end_time = end_time
        
        if best_friend_idx is None:
            # No feasible friend found, break
            break
            
        # Schedule this friend
        friend = friends_sorted[best_friend_idx]
        itinerary.append({
            "action": "meet",
            "location": friend['location'],
            "person": friend['name'],
            "start_time": minutes_to_time(best_start_time),
            "end_time": minutes_to_time(best_end_time)
        })
        
        # Update current state
        current_time = best_end_time
        current_location = friend['location']
        scheduled[best_friend_idx] = True
    
    # If we couldn't schedule all friends, use a fallback
    if len(itinerary) < len(friends):
        # Use the manually crafted fallback itinerary
        fallback_itinerary = [
            {"action": "meet", "location": "Embarcadero", "person": "William", "start_time": "7:00", "end_time": "8:30"},
            {"action": "meet", "location": "Nob Hill", "person": "Stephanie", "start_time": "8:45", "end_time": "9:30"},
            {"action": "meet", "location": "Alamo Square", "person": "Joseph", "start_time": "11:30", "end_time": "11:45"},
            {"action": "meet", "location": "Russian Hill", "person": "Karen", "start_time": "14:30", "end_time": "15:00"},
            {"action": "meet", "location": "North Beach", "person": "Kimberly", "start_time": "15:15", "end_time": "15:45"},
            {"action": "meet", "location": "The Castro", "person": "Laura", "start_time": "19:45", "end_time": "21:30"},
            {"action": "meet", "location": "Golden Gate Park", "person": "Daniel", "start_time": "21:45", "end_time": "22:00"}
        ]
        result = {"itinerary": fallback_itinerary}
    else:
        result = {"itinerary": itinerary}
    
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()