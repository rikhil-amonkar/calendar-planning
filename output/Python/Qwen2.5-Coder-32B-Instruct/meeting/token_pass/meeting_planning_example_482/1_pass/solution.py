import json
from datetime import datetime, timedelta

# Define travel times as a dictionary of dictionaries
travel_times = {
    'Haight-Ashbury': {'Mission District': 11, 'Bayview': 18, 'Pacific Heights': 12, 'Russian Hill': 17, 'Fisherman\'s Wharf': 23},
    'Mission District': {'Haight-Ashbury': 12, 'Bayview': 15, 'Pacific Heights': 16, 'Russian Hill': 15, 'Fisherman\'s Wharf': 22},
    'Bayview': {'Haight-Ashbury': 19, 'Mission District': 13, 'Pacific Heights': 23, 'Russian Hill': 23, 'Fisherman\'s Wharf': 25},
    'Pacific Heights': {'Haight-Ashbury': 11, 'Mission District': 15, 'Bayview': 22, 'Russian Hill': 7, 'Fisherman\'s Wharf': 13},
    'Russian Hill': {'Haight-Ashbury': 17, 'Mission District': 16, 'Bayview': 23, 'Pacific Heights': 7, 'Fisherman\'s Wharf': 7},
    'Fisherman\'s Wharf': {'Haight-Ashbury': 22, 'Mission District': 22, 'Bayview': 26, 'Pacific Heights': 12, 'Russian Hill': 7}
}

# Define meeting constraints
constraints = {
    'Stephanie': {'location': 'Mission District', 'start': '8:15', 'end': '13:45', 'duration': 90},
    'Sandra': {'location': 'Bayview', 'start': '13:00', 'end': '19:30', 'duration': 15},
    'Richard': {'location': 'Pacific Heights', 'start': '7:15', 'end': '10:15', 'duration': 75},
    'Brian': {'location': 'Russian Hill', 'start': '12:15', 'end': '16:00', 'duration': 120},
    'Jason': {'location': 'Fisherman\'s Wharf', 'start': '8:30', 'end': '17:45', 'duration': 60}
}

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def add_minutes_to_time(time_obj, minutes):
    return time_obj + timedelta(minutes=minutes)

def time_to_str(time_obj):
    return time_obj.strftime('%H:%M')

def can_meet(start_time, end_time, required_start, required_end, required_duration):
    required_start_time = parse_time(required_start)
    required_end_time = parse_time(required_end)
    if start_time >= required_start_time and end_time <= required_end_time:
        if (end_time - start_time).total_seconds() / 60 >= required_duration:
            return True
    return False

def backtrack(current_location, current_time, visited, itinerary):
    global best_itinerary, best_score
    
    # Calculate score based on number of people met
    score = len(visited)
    
    # Update best itinerary if current one is better
    if score > best_score:
        best_score = score
        best_itinerary = itinerary[:]
    
    # Try to meet each friend if not already visited
    for friend, constraint in constraints.items():
        if friend not in visited:
            location = constraint['location']
            duration = constraint['duration']
            
            # Calculate travel time to the friend's location
            travel_time = travel_times[current_location][location]
            meet_start_time = add_minutes_to_time(current_time, travel_time)
            meet_end_time = add_minutes_to_time(meet_start_time, duration)
            
            # Check if we can meet the friend within their availability
            if can_meet(meet_start_time, meet_end_time, constraint['start'], constraint['end'], duration):
                # Add meeting to itinerary
                itinerary.append({
                    'action': 'meet',
                    'location': location,
                    'person': friend,
                    'start_time': time_to_str(meet_start_time),
                    'end_time': time_to_str(meet_end_time)
                })
                
                # Recurse with updated state
                backtrack(location, meet_end_time, visited | {friend}, itinerary)
                
                # Backtrack
                itinerary.pop()

best_itinerary = []
best_score = 0

# Start backtracking from Haight-Ashbury at 9:00 AM
backtrack('Haight-Ashbury', parse_time('9:00'), set(), [])

# Output the best itinerary in JSON format
print(json.dumps({"itinerary": best_itinerary}, indent=2))