import json
from itertools import permutations

def minutes_to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Define travel times between locations
travel_times = {
    ('Embarcadero', 'Financial District'): 5,
    ('Embarcadero', 'Alamo Square'): 19,
    ('Financial District', 'Embarcadero'): 4,
    ('Financial District', 'Alamo Square'): 17,
    ('Alamo Square', 'Embarcadero'): 17,
    ('Alamo Square', 'Financial District'): 17,
}

# Define friends' constraints
friends = [
    {
        'name': 'Stephanie',
        'location': 'Financial District',
        'start_time': 8 * 60 + 15,  # 8:15 AM in minutes
        'end_time': 11 * 60 + 30,   # 11:30 AM in minutes
        'min_duration': 90         # Minimum meeting duration in minutes
    },
    {
        'name': 'John',
        'location': 'Alamo Square',
        'start_time': 10 * 60 + 15, # 10:15 AM in minutes
        'end_time': 20 * 60 + 45,   # 8:45 PM in minutes
        'min_duration': 30         # Minimum meeting duration in minutes
    }
]

best_itinerary = None
max_friends = 0

# Try all permutations of friends to find the optimal order
for order in permutations(friends):
    current_time = 9 * 60  # Start at Embarcadero at 9:00 AM (540 minutes)
    current_location = 'Embarcadero'
    itinerary = []
    feasible = True
    
    for friend in order:
        # Calculate travel time to the friend's location
        travel_time = travel_times.get((current_location, friend['location']), None)
        if travel_time is None:
            feasible = False
            break
        
        arrival_time = current_time + travel_time
        
        # Determine the earliest and latest possible start times for the meeting
        friend_start = friend['start_time']
        friend_end = friend['end_time']
        min_duration = friend['min_duration']
        
        earliest_start = max(arrival_time, friend_start)
        latest_start = friend_end - min_duration
        
        if earliest_start > latest_start:
            feasible = False
            break
        
        # Schedule the meeting
        meeting_start = earliest_start
        meeting_end = meeting_start + min_duration
        
        itinerary.append({
            'name': friend['name'],
            'location': friend['location'],
            'start': meeting_start,
            'end': meeting_end
        })
        
        # Update current time and location
        current_time = meeting_end
        current_location = friend['location']
    
    # Check if this itinerary is better than the previous best
    if feasible and len(itinerary) > max_friends:
        max_friends = len(itinerary)
        best_itinerary = itinerary

# Convert the best itinerary to the required JSON format
result = {"itinerary": []}
if best_itinerary:
    for meeting in best_itinerary:
        result["itinerary"].append({
            "action": "meet",
            "location": meeting['location'],
            "person": meeting['name'],
            "start_time": minutes_to_time_str(meeting['start']),
            "end_time": minutes_to_time_str(meeting['end'])
        })

print(json.dumps(result, indent=2))