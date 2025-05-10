def convert_minutes(minutes):
    hours = minutes // 60
    mins = minutes % 60
    if hours == 0:
        return '9:00'
    else:
        return f"{hours}:{mins:02d}"

locations = {
    'North Beach': {
        'Mission District': 18,
        'The Castro': 22
    },
    'Mission District': {
        'North Beach': 17,
        'The Castro': 7
    },
    'The Castro': {
        'North Beach': 20,
        'Mission District': 7
    }
}

people = [
    {'name': 'James', 'location': 'Mission District', 'start': 570, 'end': 690, 'min': 75},
    {'name': 'Robert', 'location': 'The Castro', 'start': 570, 'end': 720, 'min': 30}
]

people_sorted = sorted(people, key=lambda x: (x['end'] - x['min']))

current_time = 0
current_location = 'North Beach'
itinerary = []

for person in people_sorted:
    location = person['location']
    travel_time = locations[current_location][location]
    arrival_time = current_time + travel_time
    latest_start = person['end'] - person['min']
    if arrival_time <= latest_start:
        meeting_end = arrival_time + person['min']
        start_str = convert_minutes(arrival_time)
        end_str = convert_minutes(meeting_end)
        itinerary.append({
            'action': 'meet',
            'location': location,
            'person': person['name'],
            'start_time': start_str,
            'end_time': end_str
        })
        current_time = meeting_end
        current_location = location

print(json.dumps(itinerary))