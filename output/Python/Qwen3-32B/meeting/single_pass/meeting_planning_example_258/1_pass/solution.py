import itertools
import json

# Define travel times between locations
travel_times = {
    'Embarcadero': {
        'Presidio': 20,
        'Richmond District': 21,
        'Fisherman\'s Wharf': 6
    },
    'Presidio': {
        'Embarcadero': 20,
        'Richmond District': 7,
        'Fisherman\'s Wharf': 19
    },
    'Richmond District': {
        'Embarcadero': 19,
        'Presidio': 7,
        'Fisherman\'s Wharf': 18
    },
    'Fisherman\'s Wharf': {
        'Embarcadero': 8,
        'Presidio': 17,
        'Richmond District': 18
    }
}

# Define friends and their constraints
friends = [
    {
        'name': 'Barbara',
        'location': "Fisherman's Wharf",
        'available_start': 9 * 60 + 15,  # 9:15 AM
        'available_end': 20 * 60 + 15,   # 8:15 PM
        'required': 120  # minutes
    },
    {
        'name': 'Betty',
        'location': 'Presidio',
        'available_start': 10 * 60 + 15,  # 10:15 AM
        'available_end': 21 * 60 + 30,    # 9:30 PM
        'required': 45  # minutes
    },
    {
        'name': 'David',
        'location': 'Richmond District',
        'available_start': 13 * 60,       # 1:00 PM
        'available_end': 20 * 60 + 15,    # 8:15 PM
        'required': 90  # minutes
    }
]

def minutes_to_time_str(minutes):
    """Convert minutes since midnight to H:MM format"""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def is_valid_sequence(sequence):
    """Check if a sequence of friends can be visited with all constraints"""
    current_time = 9 * 60  # Start at 9:00 AM
    current_location = 'Embarcadero'
    meetings = []
    
    for friend in sequence:
        # Calculate travel time
        travel_time = travel_times[current_location][friend['location']]
        arrival_time = current_time + travel_time
        
        # Check if meeting is possible
        available_start = friend['available_start']
        available_end = friend['available_end']
        required = friend['required']
        
        earliest_start = max(arrival_time, available_start)
        latest_start = available_end - required
        
        if earliest_start > latest_start:
            return None  # This sequence is invalid
        
        # Schedule the meeting
        meeting_start = earliest_start
        meeting_end = meeting_start + required
        
        meetings.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': minutes_to_time_str(meeting_start),
            'end_time': minutes_to_time_str(meeting_end)
        })
        
        # Update current time and location
        current_time = meeting_end
        current_location = friend['location']
    
    return meetings

# Find the best valid sequence
valid_sequences = []
for perm in itertools.permutations(friends):
    meetings = is_valid_sequence(perm)
    if meetings:
        valid_sequences.append(meetings)

# Output the first valid sequence (which meets all 3 friends)
result = {
    "itinerary": valid_sequences[0] if valid_sequences else []
}

print(json.dumps(result, indent=2))