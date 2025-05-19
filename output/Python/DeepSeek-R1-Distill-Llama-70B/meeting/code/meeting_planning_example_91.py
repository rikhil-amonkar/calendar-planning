import json

# Travel times in minutes between locations
travel_times = {
    'Russian Hill': {
        'Richmond District': 14,
    },
    'Richmond District': {
        'Russian Hill': 13,
    }
}

# Friend's data
friends = [
    {
        'name': 'Daniel',
        'location': 'Richmond District',
        'start': '19:00',
        'end': '20:15',
        'duration': 75,
    }
]

# Convert time strings to minutes
def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

# Convert minutes to time string
def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Calculate the optimal meeting time
current_time = 540  # 9:00 AM in minutes
current_location = 'Russian Hill'

# Calculate earliest arrival time at Richmond District
travel_time = travel_times[current_location]['Richmond District']
arrival_time = current_time + travel_time

# Convert friend's availability to minutes
start_time = time_to_minutes(friends[0]['start'])
end_time = time_to_minutes(friends[0]['end'])
duration = friends[0]['duration']

# Calculate latest possible start time to meet duration requirement
latest_start = end_time - duration

# Determine the best start time within the available window
meeting_start = max(arrival_time, start_time)
meeting_end = meeting_start + duration

# Check if meeting fits within available time
if meeting_start > latest_start:
    print("No valid meeting time found.")
else:
    # Prepare the itinerary
    itinerary = [{
        'action': 'meet',
        'location': friends[0]['location'],
        'person': friends[0]['name'],
        'start_time': minutes_to_time(meeting_start),
        'end_time': minutes_to_time(meeting_end)
    }]
    
    # Output the result
    result = {
        "itinerary": itinerary
    }
    
    print(json.dumps(result))