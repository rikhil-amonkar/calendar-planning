import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Golden Gate Park', 'Marina District'): 16,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Golden Gate Park', 'Union Square'): 22,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Haight-Ashbury', 'Sunset District'): 15,
    ('Haight-Ashbury', 'Marina District'): 17,
    ('Haight-Ashbury', 'Financial District'): 21,
    ('Haight-Ashbury', 'Union Square'): 17,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Sunset District', 'Marina District'): 21,
    ('Sunset District', 'Financial District'): 30,
    ('Sunset District', 'Union Square'): 30,
    ('Marina District', 'Golden Gate Park'): 18,
    ('Marina District', 'Haight-Ashbury'): 16,
    ('Marina District', 'Sunset District'): 19,
    ('Marina District', 'Financial District'): 17,
    ('Marina District', 'Union Square'): 16,
    ('Financial District', 'Golden Gate Park'): 23,
    ('Financial District', 'Haight-Ashbury'): 19,
    ('Financial District', 'Sunset District'): 31,
    ('Financial District', 'Marina District'): 15,
    ('Financial District', 'Union Square'): 9,
    ('Union Square', 'Golden Gate Park'): 22,
    ('Union Square', 'Haight-Ashbury'): 18,
    ('Union Square', 'Sunset District'): 26,
    ('Union Square', 'Marina District'): 18,
    ('Union Square', 'Financial District'): 9,
}

# Define friends' availability
friends = {
    'Sarah': {'location': 'Haight-Ashbury', 'start': 1700, 'end': 2130, 'min_duration': 105},
    'Patricia': {'location': 'Sunset District', 'start': 1700, 'end': 1945, 'min_duration': 45},
    'Matthew': {'location': 'Marina District', 'start': 915, 'end': 1200, 'min_duration': 15},
    'Joseph': {'location': 'Financial District', 'start': 1415, 'end': 1845, 'min_duration': 30},
    'Robert': {'location': 'Union Square', 'start': 1015, 'end': 2145, 'min_duration': 15},
}

def convert_to_24h_format(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def backtrack(current_location, current_time, visited_friends, itinerary):
    global best_itinerary
    
    # If we've visited all friends, check if this itinerary is better than the best found so far
    if len(visited_friends) == len(friends):
        if len(itinerary) > len(best_itinerary):
            best_itinerary = itinerary[:]
        return
    
    # Try to meet each friend
    for friend, details in friends.items():
        if friend not in visited_friends:
            travel_time = travel_times[(current_location, details['location'])]
            meet_start_time = current_time + travel_time
            
            # Check if we can meet this friend within their availability
            if meet_start_time + details['min_duration'] <= details['end']:
                meet_end_time = meet_start_time + details['min_duration']
                itinerary.append({
                    "action": "meet",
                    "location": details['location'],
                    "person": friend,
                    "start_time": convert_to_24h_format(meet_start_time),
                    "end_time": convert_to_24h_format(meet_end_time)
                })
                
                backtrack(details['location'], meet_end_time, visited_friends | {friend}, itinerary)
                
                # Backtrack
                itinerary.pop()

# Initialize the best itinerary
best_itinerary = []

# Start backtracking from Golden Gate Park at 9:00 AM (540 minutes after midnight)
backtrack('Golden Gate Park', 540, set(), [])

# Output the best itinerary as JSON
output = {
    "itinerary": best_itinerary
}

print(json.dumps(output, indent=2))