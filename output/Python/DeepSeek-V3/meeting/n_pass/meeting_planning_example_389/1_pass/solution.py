import json
from itertools import permutations

def time_to_minutes(time_str):
    """Convert time string 'H:MM' to minutes since midnight."""
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    """Convert minutes since midnight to time string 'H:MM'."""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Travel times in minutes between locations
travel_times = {
    'Haight-Ashbury': {
        'Fisherman\'s Wharf': 23,
        'Richmond District': 10,
        'Mission District': 11,
        'Bayview': 18
    },
    'Fisherman\'s Wharf': {
        'Haight-Ashbury': 22,
        'Richmond District': 18,
        'Mission District': 22,
        'Bayview': 26
    },
    'Richmond District': {
        'Haight-Ashbury': 10,
        'Fisherman\'s Wharf': 18,
        'Mission District': 20,
        'Bayview': 26
    },
    'Mission District': {
        'Haight-Ashbury': 12,
        'Fisherman\'s Wharf': 22,
        'Richmond District': 20,
        'Bayview': 15
    },
    'Bayview': {
        'Haight-Ashbury': 19,
        'Fisherman\'s Wharf': 25,
        'Richmond District': 25,
        'Mission District': 13
    }
}

# Meeting constraints
meetings = [
    {
        'person': 'Sarah',
        'location': 'Fisherman\'s Wharf',
        'available_start': '14:45',
        'available_end': '17:30',
        'duration': 105
    },
    {
        'person': 'Mary',
        'location': 'Richmond District',
        'available_start': '13:00',
        'available_end': '19:15',
        'duration': 75
    },
    {
        'person': 'Helen',
        'location': 'Mission District',
        'available_start': '21:45',
        'available_end': '22:30',
        'duration': 30
    },
    {
        'person': 'Thomas',
        'location': 'Bayview',
        'available_start': '15:15',
        'available_end': '18:45',
        'duration': 120
    }
]

# Initial state
current_location = 'Haight-Ashbury'
current_time = time_to_minutes('9:00')
itinerary = []

# Generate all possible meeting orders
meeting_orders = permutations(meetings)

best_itinerary = None
best_meetings_met = 0

for order in meeting_orders:
    temp_itinerary = []
    temp_current_location = current_location
    temp_current_time = current_time
    meetings_met = 0
    
    for meeting in order:
        # Calculate travel time to meeting location
        travel_time = travel_times[temp_current_location][meeting['location']]
        arrival_time = temp_current_time + travel_time
        
        # Calculate meeting window
        available_start = time_to_minutes(meeting['available_start'])
        available_end = time_to_minutes(meeting['available_end'])
        
        # Determine when meeting can start
        meeting_start = max(arrival_time, available_start)
        meeting_end = meeting_start + meeting['duration']
        
        # Check if meeting can fit
        if meeting_end <= available_end:
            temp_itinerary.append({
                'action': 'meet',
                'location': meeting['location'],
                'person': meeting['person'],
                'start_time': minutes_to_time(meeting['available_start']),
                'end_time': minutes_to_time(meeting['available_end'])
            })
            meetings_met += 1
            temp_current_location = meeting['location']
            temp_current_time = meeting_end
    
    # Update best itinerary if this order meets more meetings
    if meetings_met > best_meetings_met:
        best_meetings_met = meetings_met
        best_itinerary = temp_itinerary

# Prepare the output
output = {
    "itinerary": best_itinerary
}

print(json.dumps(output, indent=2))