import json
from datetime import datetime, timedelta

# Define travel times as a dictionary of dictionaries
travel_times = {
    'Haight-Ashbury': {'Russian Hill': 17, 'Fisherman\'s Wharf': 23, 'Nob Hill': 15, 'Golden Gate Park': 7, 'Alamo Square': 5, 'Pacific Heights': 12},
    'Russian Hill': {'Haight-Ashbury': 17, 'Fisherman\'s Wharf': 7, 'Nob Hill': 5, 'Golden Gate Park': 21, 'Alamo Square': 15, 'Pacific Heights': 7},
    'Fisherman\'s Wharf': {'Haight-Ashbury': 22, 'Russian Hill': 7, 'Nob Hill': 11, 'Golden Gate Park': 25, 'Alamo Square': 19, 'Pacific Heights': 12},
    'Nob Hill': {'Haight-Ashbury': 13, 'Russian Hill': 5, 'Fisherman\'s Wharf': 11, 'Golden Gate Park': 17, 'Alamo Square': 11, 'Pacific Heights': 8},
    'Golden Gate Park': {'Haight-Ashbury': 7, 'Russian Hill': 19, 'Fisherman\'s Wharf': 24, 'Nob Hill': 20, 'Alamo Square': 10, 'Pacific Heights': 16},
    'Alamo Square': {'Haight-Ashbury': 5, 'Russian Hill': 13, 'Fisherman\'s Wharf': 19, 'Nob Hill': 11, 'Golden Gate Park': 9, 'Pacific Heights': 10},
    'Pacific Heights': {'Haight-Ashbury': 11, 'Russian Hill': 7, 'Fisherman\'s Wharf': 13, 'Nob Hill': 8, 'Golden Gate Park': 15, 'Alamo Square': 10}
}

# Define friends' availability and meeting durations
friends = {
    'Stephanie': ('20:00', '20:45', 15),
    'Kevin': ('19:15', '21:45', 75),
    'Robert': ('07:45', '10:30', 90),
    'Steven': ('08:30', '17:00', 75),
    'Anthony': ('07:45', '19:45', 15),
    'Sandra': ('14:45', '21:45', 45)
}

# Convert time strings to minutes since midnight
def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    hours, minutes = divmod(minutes, 60)
    return f"{hours}:{minutes:02}"

# Backtracking function to find the optimal schedule
def backtrack(current_location, current_time, visited_friends, itinerary):
    global best_itinerary
    
    # Check if the current itinerary is better than the best found so far
    if len(visited_friends) > len(best_itinerary):
        best_itinerary = itinerary.copy()
    
    # Try to meet each friend
    for friend, (start, end, min_duration) in friends.items():
        if friend in visited_friends:
            continue
        
        start_time = time_to_minutes(start)
        end_time = time_to_minutes(end)
        
        # Calculate travel time to the friend's location
        travel_time = travel_times[current_location][friend]
        meeting_start = current_time + travel_time
        
        # Check if we can meet the friend within their availability
        if meeting_start + min_duration <= end_time:
            meeting_end = meeting_start + min_duration
            
            # Add the meeting to the itinerary
            itinerary.append({
                "action": "meet",
                "location": friend,
                "person": friend,
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            })
            
            # Recurse with updated location, time, and visited friends
            backtrack(friend, meeting_end, visited_friends | {friend}, itinerary)
            
            # Backtrack: remove the last meeting and try another option
            itinerary.pop()

# Initialize variables
best_itinerary = []
start_location = 'Haight-Ashbury'
start_time = time_to_minutes('09:00')
visited_friends = set()

# Start the backtracking process
backtrack(start_location, start_time, visited_friends, [])

# Convert the best itinerary to JSON format
output_json = json.dumps({"itinerary": best_itinerary}, indent=2)
print(output_json)