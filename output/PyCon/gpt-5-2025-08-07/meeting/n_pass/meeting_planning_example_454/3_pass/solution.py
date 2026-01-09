import json
from datetime import datetime, timedelta
import itertools

def time_to_minutes(time_str):
    """Convert time string (H:MM) to minutes since midnight"""
    if isinstance(time_str, str):
        dt = datetime.strptime(time_str, "%H:%M")
    else:
        dt = time_str
    return dt.hour * 60 + dt.minute

def minutes_to_time(minutes):
    """Convert minutes since midnight to time string (H:MM)"""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def calculate_meeting_time(current_time, current_location, friend_info, travel_times):
    """Calculate the best meeting time for a friend given current position and time"""
    location = friend_info['location']
    available_start = friend_info['available_start']
    available_end = friend_info['available_end']
    min_duration = friend_info['min_duration']
    
    # Calculate travel time
    travel_time = travel_times[current_location][location]
    
    # Earliest we can arrive
    arrival_time = current_time + travel_time
    
    # Meeting must start after arrival AND within friend's availability
    meeting_start = max(arrival_time, available_start)
    
    # Check if meeting is possible
    if meeting_start + min_duration > available_end:
        return None, 0
    
    # Use maximum possible duration within constraints
    meeting_duration = min(min_duration, available_end - meeting_start)
    
    return meeting_start, meeting_duration

def find_best_itinerary(start_time, start_location, friends, travel_times):
    """Find the best itinerary using backtracking with pruning"""
    best_itinerary = []
    best_total_duration = 0
    
    def backtrack(current_time, current_location, visited, itinerary, total_duration):
        nonlocal best_itinerary, best_total_duration
        
        # If we found a better solution, update
        if total_duration > best_total_duration:
            best_total_duration = total_duration
            best_itinerary = itinerary.copy()
        
        # Try to visit each unvisited friend
        for friend, info in friends.items():
            if friend in visited:
                continue
                
            meeting_start, meeting_duration = calculate_meeting_time(
                current_time, current_location, info, travel_times
            )
            
            if meeting_duration > 0:  # Valid meeting
                new_visited = visited | {friend}
                new_itinerary = itinerary + [(friend, info['location'], meeting_start, meeting_duration)]
                new_total_duration = total_duration + meeting_duration
                
                backtrack(
                    meeting_start + meeting_duration,
                    info['location'],
                    new_visited,
                    new_itinerary,
                    new_total_duration
                )
    
    # Start backtracking
    backtrack(start_time, start_location, set(), [], 0)
    return best_itinerary

def main():
    # Travel times matrix (in minutes)
    travel_times = {
        'Presidio': {
            'Golden Gate Park': 12, 'Bayview': 31, 'Chinatown': 21, 
            'North Beach': 18, 'Mission District': 26
        },
        'Golden Gate Park': {
            'Presidio': 11, 'Bayview': 23, 'Chinatown': 23, 
            'North Beach': 24, 'Mission District': 17
        },
        'Bayview': {
            'Presidio': 31, 'Golden Gate Park': 22, 'Chinatown': 18, 
            'North Beach': 21, 'Mission District': 13
        },
        'Chinatown': {
            'Presidio': 19, 'Golden Gate Park': 23, 'Bayview': 22, 
            'North Beach': 3, 'Mission District': 18
        },
        'North Beach': {
            'Presidio': 17, 'Golden Gate Park': 22, 'Bayview': 22, 
            'Chinatown': 6, 'Mission District': 18
        },
        'Mission District': {
            'Presidio': 25, 'Golden Gate Park': 17, 'Bayview': 15, 
            'Chinatown': 16, 'North Beach': 17
        }
    }

    # Friend constraints
    friends = {
        'Jessica': {
            'location': 'Golden Gate Park',
            'available_start': time_to_minutes('13:45'),  # 1:45 PM
            'available_end': time_to_minutes('15:00'),    # 3:00 PM
            'min_duration': 30
        },
        'Ashley': {
            'location': 'Bayview',
            'available_start': time_to_minutes('17:15'),  # 5:15 PM
            'available_end': time_to_minutes('20:00'),    # 8:00 PM
            'min_duration': 105
        },
        'Ronald': {
            'location': 'Chinatown',
            'available_start': time_to_minutes('7:15'),   # 7:15 AM
            'available_end': time_to_minutes('14:45'),    # 2:45 PM
            'min_duration': 90
        },
        'William': {
            'location': 'North Beach',
            'available_start': time_to_minutes('13:15'),  # 1:15 PM
            'available_end': time_to_minutes('20:15'),    # 8:15 PM
            'min_duration': 15
        },
        'Daniel': {
            'location': 'Mission District',
            'available_start': time_to_minutes('7:00'),   # 7:00 AM
            'available_end': time_to_minutes('11:15'),    # 11:15 AM
            'min_duration': 105
        }
    }

    # Start at Presidio at 9:00 AM
    start_time = time_to_minutes('9:00')
    start_location = 'Presidio'

    # Find best itinerary
    best_sequence = find_best_itinerary(start_time, start_location, friends, travel_times)
    
    # Build itinerary
    itinerary = []
    current_time = start_time
    current_location = start_location
    
    for friend, location, meeting_start, meeting_duration in best_sequence:
        # Add travel if needed
        if current_location != location:
            travel_time = travel_times[current_location][location]
            travel_start = minutes_to_time(current_time)
            travel_end = minutes_to_time(current_time + travel_time)
            itinerary.append({
                "action": "travel",
                "from": current_location,
                "to": location,
                "start_time": travel_start,
                "end_time": travel_end
            })
            current_time += travel_time
        
        # Add meeting
        meeting_end_time = meeting_start + meeting_duration
        meeting_start_str = minutes_to_time(meeting_start)
        meeting_end_str = minutes_to_time(meeting_end_time)
        itinerary.append({
            "action": "meet",
            "location": location,
            "person": friend,
            "start_time": meeting_start_str,
            "end_time": meeting_end_str
        })
        
        current_time = meeting_end_time
        current_location = location

    # Output result
    result = {
        "itinerary": itinerary
    }
    
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()