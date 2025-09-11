import json

def time_to_minutes(t):
    h, m = map(int, t.split(':'))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    m %= 60
    return f"{h}:{m:02d}"

# Input parameters
travel_times = {
    ('North Beach', 'Union Square'): 7,
    ('North Beach', 'Russian Hill'): 4,
    ('Union Square', 'North Beach'): 10,
    ('Union Square', 'Russian Hill'): 13,
    ('Russian Hill', 'North Beach'): 5,
    ('Russian Hill', 'Union Square'): 11,
}

# Initial conditions
start_location = 'North Beach'
start_time = time_to_minutes('9:00')  # 9:00 AM

# Friends' constraints
friends = [
    {
        'name': 'Emily',
        'location': 'Union Square',
        'available_start': time_to_minutes('16:00'),
        'available_end': time_to_minutes('17:15'),
        'required_duration': 45
    },
    {
        'name': 'Margaret',
        'location': 'Russian Hill',
        'available_start': time_to_minutes('19:00'),
        'available_end': time_to_minutes('21:00'),
        'required_duration': 120
    }
]

current_time = start_time
current_location = start_location
itinerary = []

# Try to meet Emily first
emily = friends[0]
margaret = friends[1]

# Check if Emily can be met
dest = emily['location']
travel_time = travel_times.get((current_location, dest), float('inf'))
arrival_time = emily['available_start']  # Need to arrive by this time
departure_time = arrival_time - travel_time

if departure_time >= current_time:
    # Can leave current_location and arrive on time
    # Meeting starts at available_start, ends at available_start + duration
    meeting_start = emily['available_start']
    meeting_end = meeting_start + emily['required_duration']
    if meeting_end <= emily['available_end']:
        # Add to itinerary
        itinerary.append({
            'action': 'meet',
            'location': dest,
            'person': emily['name'],
            'start_time': minutes_to_time(meeting_start),
            'end_time': minutes_to_time(meeting_end)
        })
        # Update current time and location
        current_time = meeting_end
        current_location = dest
        # Now try to meet Margaret
        dest_margaret = margaret['location']
        travel_time_m = travel_times.get((current_location, dest_margaret), float('inf'))
        # Need to arrive by margaret's start time
        arrival_time_m = margaret['available_start']
        departure_time_m = arrival_time_m - travel_time_m
        if departure_time_m >= current_time:
            # Depart immediately, arrive at current_time + travel_time_m
            arrival_time_m Actual arrival is current_time + travel_time_m
            arrival_time_m_actual = current_time + travel_time_m
            # Wait until available_start if needed
            meeting_start_m = max(arrival_time_m_actual, margaret['available_start'])
            meeting_end_m = meeting_start_m + margaret['required_duration']
            if meeting_end_m <= margaret['available_end']:
                itinerary.append({
                    'action': 'meet',
                    'location': dest_margaret,
                    'person': margaret['name'],
                    'start_time': minutes_to_time(meeting_start_m),
                    'end_time': minutes_to_time(meeting_end_m)
                })
                current_time = meeting_end_m
                current_location = dest_margaret
        else:
            # Can't meet Margaret
            pass

# Output the itinerary as JSON
result = {'itinerary': itinerary}
print(json.dumps(result, indent=2))