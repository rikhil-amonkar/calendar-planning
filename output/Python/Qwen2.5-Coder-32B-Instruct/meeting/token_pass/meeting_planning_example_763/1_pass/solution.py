import json
from collections import defaultdict

# Travel times represented as a graph
travel_times = {
    'Chinatown': {'Embarcadero': 5, 'Pacific Heights': 10, 'Russian Hill': 7, 'Haight-Ashbury': 19, 'Golden Gate Park': 23, 'Fisherman\'s Wharf': 8, 'Sunset District': 29, 'The Castro': 22},
    'Embarcadero': {'Chinatown': 7, 'Pacific Heights': 11, 'Russian Hill': 8, 'Haight-Ashbury': 21, 'Golden Gate Park': 25, 'Fisherman\'s Wharf': 6, 'Sunset District': 30, 'The Castro': 25},
    'Pacific Heights': {'Chinatown': 11, 'Embarcadero': 10, 'Russian Hill': 7, 'Haight-Ashbury': 11, 'Golden Gate Park': 15, 'Fisherman\'s Wharf': 13, 'Sunset District': 21, 'The Castro': 16},
    'Russian Hill': {'Chinatown': 9, 'Embarcadero': 8, 'Pacific Heights': 7, 'Haight-Ashbury': 17, 'Golden Gate Park': 21, 'Fisherman\'s Wharf': 7, 'Sunset District': 23, 'The Castro': 21},
    'Haight-Ashbury': {'Chinatown': 19, 'Embarcadero': 20, 'Pacific Heights': 12, 'Russian Hill': 17, 'Golden Gate Park': 7, 'Fisherman\'s Wharf': 23, 'Sunset District': 15, 'The Castro': 6},
    'Golden Gate Park': {'Chinatown': 23, 'Embarcadero': 25, 'Pacific Heights': 16, 'Russian Hill': 19, 'Haight-Ashbury': 7, 'Fisherman\'s Wharf': 24, 'Sunset District': 10, 'The Castro': 13},
    'Fisherman\'s Wharf': {'Chinatown': 12, 'Embarcadero': 8, 'Pacific Heights': 12, 'Russian Hill': 7, 'Haight-Ashbury': 22, 'Golden Gate Park': 25, 'Sunset District': 27, 'The Castro': 27},
    'Sunset District': {'Chinatown': 30, 'Embarcadero': 30, 'Pacific Heights': 21, 'Russian Hill': 24, 'Haight-Ashbury': 15, 'Golden Gate Park': 11, 'Fisherman\'s Wharf': 29, 'The Castro': 17},
    'The Castro': {'Chinatown': 22, 'Embarcadero': 22, 'Pacific Heights': 16, 'Russian Hill': 18, 'Haight-Ashbury': 6, 'Golden Gate Park': 11, 'Fisherman\'s Wharf': 24, 'Sunset District': 17},
}

# Meeting constraints
meetings = {
    'Richard': {'location': 'Embarcadero', 'start': 15*60+15, 'end': 18*60+45, 'duration': 90},
    'Mark': {'location': 'Pacific Heights', 'start': 15*60, 'end': 17*60, 'duration': 45},
    'Matthew': {'location': 'Russian Hill', 'start': 17*60+30, 'end': 21*60, 'duration': 90},
    'Rebecca': {'location': 'Haight-Ashbury', 'start': 14*60+45, 'end': 18*60, 'duration': 60},
    'Melissa': {'location': 'Golden Gate Park', 'start': 13*60+45, 'end': 17*60+30, 'duration': 90},
    'Margaret': {'location': 'Fisherman\'s Wharf', 'start': 14*60+45, 'end': 20*60+15, 'duration': 15},
    'Emily': {'location': 'Sunset District', 'start': 15*60+45, 'end': 17*60, 'duration': 45},
    'George': {'location': 'The Castro', 'start': 14*60, 'end': 16*60+15, 'duration': 75},
}

# Convert time to string format HH:MM
def time_to_str(minutes):
    hours, mins = divmod(minutes, 60)
    return f"{hours}:{mins}"

# Backtracking function to find the optimal schedule
def backtrack(current_location, current_time, visited_meetings, itinerary):
    global best_itinerary, best_meeting_time
    
    # Calculate total meeting time
    current_meeting_time = sum(meet['duration'] for meet in visited_meetings.values())
    
    # Update best itinerary if current one is better
    if current_meeting_time > best_meeting_time:
        best_meeting_time = current_meeting_time
        best_itinerary = itinerary[:]
    
    # Try to visit each location
    for person, details in meetings.items():
        if person not in visited_meetings:
            location = details['location']
            start = details['start']
            end = details['end']
            duration = details['duration']
            
            # Calculate travel time and new start time
            travel_time = travel_times[current_location][location]
            new_start_time = current_time + travel_time
            
            # Check if meeting can be scheduled
            if new_start_time + duration <= end:
                # Schedule the meeting
                itinerary.append({
                    "action": "meet",
                    "location": location,
                    "person": person,
                    "start_time": time_to_str(new_start_time),
                    "end_time": time_to_str(new_start_time + duration)
                })
                visited_meetings[person] = True
                
                # Recurse
                backtrack(location, new_start_time + duration, visited_meetings, itinerary)
                
                # Backtrack
                itinerary.pop()
                del visited_meetings[person]

# Initialize global variables
best_itinerary = []
best_meeting_time = 0

# Start the backtracking from Chinatown at 9:00 AM (540 minutes)
backtrack('Chinatown', 9*60, {}, [])

# Output the best itinerary as JSON
output = {
    "itinerary": best_itinerary
}
print(json.dumps(output, indent=2))