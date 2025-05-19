import json

def time_to_minutes(time_str):
    hours, mins = map(int, time_str.split(':'))
    return hours * 60 + mins

def minutes_to_time(mins):
    hours = mins // 60
    mins = mins % 60
    return f"{hours}:{mins:02d}"

travel_times = {
    ('Nob Hill', 'Presidio'): 17,
    ('Presidio', 'Nob Hill'): 18
}

friends = [
    {
        'name': 'Robert',
        'location': 'Presidio',
        'available_start': '11:15',
        'available_end': '17:45',
        'required_duration': 120
    }
]

current_time = 540  # 9:00 AM in minutes
current_location = 'Nob Hill'

itinerary = []

# Calculate travel time to Presidio
travel = travel_times.get((current_location, friends[0]['location']), None)
if travel is not None:
    arrival_time = current_time + travel
    avail_start = time_to_minutes(friends[0]['available_start'])
    avail_end = time_to_minutes(friends[0]['available_end'])
    
    # Calculate earliest possible start time
    start_time = max(arrival_time, avail_start)
    end_time = start_time + friends[0]['required_duration']
    
    if end_time <= avail_end:
        itinerary.append({
            'action': 'meet',
            'location': friends[0]['location'],
            'person': friends[0]['name'],
            'start_time': minutes_to_time(start_time),
            'end_time': minutes_to_time(end_time)
        })

result = {'itinerary': itinerary}
print(json.dumps(result))