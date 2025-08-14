import itertools
import json

# Define travel times between locations in minutes
travel_times = {
    ('Castro', 'Mission District'): 7,
    ('Castro', 'Financial District'): 20,
    ('Mission District', 'Castro'): 7,
    ('Mission District', 'Financial District'): 17,
    ('Financial District', 'Castro'): 23,
    ('Financial District', 'Mission District'): 17,
}

# Define meeting constraints for each person
people = [
    {
        'name': 'Anthony',
        'location': 'Financial District',
        'earliest': 750,  # 12:30 PM in minutes since midnight
        'latest': 885,    # 2:45 PM in minutes since midnight
        'duration': 30    # Minimum meeting duration in minutes
    },
    {
        'name': 'Laura',
        'location': 'Mission District',
        'earliest': 735,  # 12:15 PM in minutes since midnight
        'latest': 1185,   # 7:45 PM in minutes since midnight
        'duration': 75    # Minimum meeting duration in minutes
    }
]

# Starting time and location
start_time_minutes = 9 * 60  # 9:00 AM in minutes since midnight
start_location = 'Castro'

def to_time_str(minutes):
    """Convert minutes since midnight to 24-hour format string like '9:00' or '13:30'"""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Check all possible meeting order permutations
for perm in itertools.permutations(people):
    current_time = start_time_minutes
    current_location = start_location
    itinerary = []
    valid = True
    
    for person in perm:
        next_location = person['location']
        
        # Add travel time
        travel_key = (current_location, next_location)
        if travel_key not in travel_times:
            valid = False
            break
        current_time += travel_times[travel_key]
        
        # Wait if necessary before meeting starts
        if current_time < person['earliest']:
            current_time = person['earliest']
            
        # Check if meeting can fit in available time window
        meeting_end = current_time + person['duration']
        if meeting_end > person['latest']:
            valid = False
            break
            
        # Add meeting to itinerary
        itinerary.append({
            'action': 'meet',
            'location': next_location,
            'person': person['name'],
            'start_time': to_time_str(current_time),
            'end_time': to_time_str(meeting_end)
        })
        
        current_location = next_location
    
    if valid:
        result = {"itinerary": itinerary}
        print(json.dumps(result))
        break