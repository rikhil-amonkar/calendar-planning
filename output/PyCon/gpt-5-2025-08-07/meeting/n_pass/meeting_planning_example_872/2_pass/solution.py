from datetime import datetime, timedelta
import json

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
    # Travel times in minutes (symmetric)
    travel_times = {
        ('Presidio', 'Haight-Ashbury'): 15,
        ('Presidio', 'Nob Hill'): 18,
        ('Presidio', 'Russian Hill'): 14,
        ('Presidio', 'North Beach'): 18,
        ('Presidio', 'Chinatown'): 21,
        ('Presidio', 'Union Square'): 22,
        ('Presidio', 'Embarcadero'): 20,
        ('Presidio', 'Financial District'): 23,
        ('Presidio', 'Marina District'): 11,
        ('Haight-Ashbury', 'Nob Hill'): 15,
        ('Haight-Ashbury', 'Russian Hill'): 17,
        ('Haight-Ashbury', 'North Beach'): 19,
        ('Haight-Ashbury', 'Chinatown'): 19,
        ('Haight-Ashbury', 'Union Square'): 19,
        ('Haight-Ashbury', 'Embarcadero'): 20,
        ('Haight-Ashbury', 'Financial District'): 21,
        ('Haight-Ashbury', 'Marina District'): 17,
        ('Nob Hill', 'Russian Hill'): 5,
        ('Nob Hill', 'North Beach'): 8,
        ('Nob Hill', 'Chinatown'): 6,
        ('Nob Hill', 'Union Square'): 7,
        ('Nob Hill', 'Embarcadero'): 9,
        ('Nob Hill', 'Financial District'): 9,
        ('Nob Hill', 'Marina District'): 11,
        ('Russian Hill', 'North Beach'): 5,
        ('Russian Hill', 'Chinatown'): 9,
        ('Russian Hill', 'Union Square'): 10,
        ('Russian Hill', 'Embarcadero'): 8,
        ('Russian Hill', 'Financial District'): 11,
        ('Russian Hill', 'Marina District'): 7,
        ('North Beach', 'Chinatown'): 6,
        ('North Beach', 'Union Square'): 7,
        ('North Beach', 'Embarcadero'): 6,
        ('North Beach', 'Financial District'): 8,
        ('North Beach', 'Marina District'): 9,
        ('Chinatown', 'Union Square'): 7,
        ('Chinatown', 'Embarcadero'): 5,
        ('Chinatown', 'Financial District'): 5,
        ('Chinatown', 'Marina District'): 12,
        ('Union Square', 'Embarcadero'): 11,
        ('Union Square', 'Financial District'): 9,
        ('Union Square', 'Marina District'): 18,
        ('Embarcadero', 'Financial District'): 5,
        ('Embarcadero', 'Marina District'): 12,
        ('Financial District', 'Marina District'): 15,
    }
    
    # Make symmetric
    symmetric_travel = travel_times.copy()
    for (loc1, loc2), time in travel_times.items():
        symmetric_travel[(loc2, loc1)] = time
    
    # Friend constraints
    friends = [
        {'name': 'Karen', 'location': 'Haight-Ashbury', 'available_start': '21:00', 'available_end': '21:45', 'duration': 45},
        {'name': 'Jessica', 'location': 'Nob Hill', 'available_start': '13:45', 'available_end': '21:00', 'duration': 90},
        {'name': 'Brian', 'location': 'Russian Hill', 'available_start': '15:30', 'available_end': '21:45', 'duration': 60},
        {'name': 'Kenneth', 'location': 'North Beach', 'available_start': '9:45', 'available_end': '21:00', 'duration': 30},
        {'name': 'Jason', 'location': 'Chinatown', 'available_start': '8:15', 'available_end': '11:45', 'duration': 75},
        {'name': 'Stephanie', 'location': 'Union Square', 'available_start': '14:45', 'available_end': '18:45', 'duration': 105},
        {'name': 'Kimberly', 'location': 'Embarcadero', 'available_start': '9:45', 'available_end': '19:30', 'duration': 75},
        {'name': 'Steven', 'location': 'Financial District', 'available_start': '7:15', 'available_end': '21:15', 'duration': 60},
        {'name': 'Mark', 'location': 'Marina District', 'available_start': '10:15', 'available_end': '13:00', 'duration': 75}
    ]
    
    # Convert times to minutes
    for friend in friends:
        friend['available_start_min'] = time_to_minutes(friend['available_start'])
        friend['available_end_min'] = time_to_minutes(friend['available_end'])
    
    # Start at Presidio at 9:00 AM
    current_time = time_to_minutes('9:00')
    current_location = 'Presidio'
    
    itinerary = []
    scheduled_friends = []
    
    # Sort friends by earliest available time to prioritize scheduling
    friends_sorted = sorted(friends, key=lambda x: x['available_start_min'])
    
    # Try to schedule meetings in a greedy manner
    for friend in friends_sorted:
        # Skip if already scheduled
        if friend['name'] in scheduled_friends:
            continue
            
        # Calculate travel time from current location
        if current_location == friend['location']:
            travel_time = 0
        else:
            travel_time = symmetric_travel.get((current_location, friend['location']), 
                                             symmetric_travel.get((friend['location'], current_location), 0))
        
        # Earliest possible start time considering travel
        earliest_start = current_time + travel_time
        
        # Check if we can schedule within friend's availability
        if (earliest_start >= friend['available_start_min'] and 
            earliest_start + friend['duration'] <= friend['available_end_min']):
            
            # Schedule the meeting
            start_time = earliest_start
            end_time = start_time + friend['duration']
            
            itinerary.append({
                "action": "meet",
                "location": friend['location'],
                "person": friend['name'],
                "start_time": minutes_to_time(start_time),
                "end_time": minutes_to_time(end_time)
            })
            
            # Update current state
            current_time = end_time
            current_location = friend['location']
            scheduled_friends.append(friend['name'])
            
        else:
            # Try to find the earliest possible time within friend's availability
            if earliest_start < friend['available_start_min']:
                candidate_start = friend['available_start_min']
            else:
                candidate_start = earliest_start
                
            if candidate_start + friend['duration'] <= friend['available_end_min']:
                # Schedule at candidate time
                start_time = candidate_start
                end_time = start_time + friend['duration']
                
                itinerary.append({
                    "action": "meet",
                    "location": friend['location'],
                    "person": friend['name'],
                    "start_time": minutes_to_time(start_time),
                    "end_time": minutes_to_time(end_time)
                })
                
                # Update current state
                current_time = end_time
                current_location = friend['location']
                scheduled_friends.append(friend['name'])
    
    # If we didn't schedule anyone, try a different approach - prioritize by time windows
    if not itinerary:
        # Reset and try a different strategy
        current_time = time_to_minutes('9:00')
        current_location = 'Presidio'
        itinerary = []
        scheduled_friends = []
        
        # Sort by availability window length (most flexible first)
        friends_by_flexibility = sorted(friends, 
                                      key=lambda x: (x['available_end_min'] - x['available_start_min']))
        
        for friend in friends_by_flexibility:
            if friend['name'] in scheduled_friends:
                continue
                
            # Calculate travel time
            if current_location == friend['location']:
                travel_time = 0
            else:
                travel_time = symmetric_travel.get((current_location, friend['location']), 
                                                 symmetric_travel.get((friend['location'], current_location), 0))
            
            earliest_start = current_time + travel_time
            
            # Try to schedule
            if earliest_start < friend['available_start_min']:
                candidate_start = friend['available_start_min']
            else:
                candidate_start = earliest_start
                
            if candidate_start + friend['duration'] <= friend['available_end_min']:
                start_time = candidate_start
                end_time = start_time + friend['duration']
                
                itinerary.append({
                    "action": "meet",
                    "location": friend['location'],
                    "person": friend['name'],
                    "start_time": minutes_to_time(start_time),
                    "end_time": minutes_to_time(end_time)
                })
                
                current_time = end_time
                current_location = friend['location']
                scheduled_friends.append(friend['name'])
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()