import itertools
import json

def minutes_to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

friends = [
    {
        'name': 'Timothy',
        'location': 'Pacific Heights',
        'start': 540,  # 9:00 AM
        'end': 930,    # 3:30 PM
        'required': 75
    },
    {
        'name': 'David',
        'location': "Fisherman's Wharf",
        'start': 645,  # 10:45 AM
        'end': 930,    # 3:30 PM
        'required': 15
    },
    {
        'name': 'Robert',
        'location': 'Mission District',
        'start': 735,  # 12:15 PM
        'end': 1185,   # 7:45 PM
        'required': 90
    }
]

travel_times = {
    ('Financial District', "Fisherman's Wharf"): 10,
    ('Financial District', 'Pacific Heights'): 13,
    ('Financial District', 'Mission District'): 17,
    ("Fisherman's Wharf", 'Financial District'): 11,
    ("Fisherman's Wharf", 'Pacific Heights'): 12,
    ("Fisherman's Wharf", 'Mission District'): 22,
    ('Pacific Heights', 'Financial District'): 13,
    ('Pacific Heights', "Fisherman's Wharf"): 13,
    ('Pacific Heights', 'Mission District'): 15,
    ('Mission District', 'Financial District'): 17,
    ('Mission District', "Fisherman's Wharf"): 22,
    ('Mission District', 'Pacific Heights'): 16,
}

for perm in itertools.permutations(friends):
    current_time = 540  # Start at 9:00 AM
    current_location = 'Financial District'
    valid = True
    itinerary = []
    for friend in perm:
        from_loc = current_location
        to_loc = friend['location']
        # Get travel time between current location and friend's location
        try:
            travel_time = travel_times[(from_loc, to_loc)]
        except KeyError:
            valid = False
            break
        arrival_time = current_time + travel_time
        # Determine meeting start time (max of arrival and friend's start)
        meeting_start = max(arrival_time, friend['start'])
        # Check if meeting can fit
        meeting_end = meeting_start + friend['required']
        if meeting_end > friend['end']:
            valid = False
            break
        # Add to itinerary
        itinerary.append((friend, meeting_start, meeting_end))
        # Update current time and location
        current_time = meeting_end
        current_location = to_loc
    if valid:
        # Construct the JSON output
        json_itinerary = []
        for entry in itinerary:
            friend, start, end = entry
            json_itinerary.append({
                'action': 'meet',
                'location': friend['location'],
                'person': friend['name'],
                'start_time': minutes_to_time_str(start),
                'end_time': minutes_to_time_str(end)
            })
        print(json.dumps({'itinerary': json_itinerary}))
        exit()

# If no valid itinerary found (unlikely in this case)
print(json.dumps({'itinerary': []}))