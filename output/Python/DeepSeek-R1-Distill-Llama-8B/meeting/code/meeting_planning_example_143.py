def convert_minutes(minutes):
    hours = minutes // 60
    mins = minutes % 60
    if hours == 0:
        return '9:00'
    else:
        return f"{hours}:{mins:02d}"

locations = {
    'North Beach': {
        'Pacific Heights': 8,
        'Embarcadero': 6
    },
    'Pacific Heights': {
        'North Beach': 9,
        'Embarcadero': 10
    },
    'Embarcadero': {
        'North Beach': 5,
        'Pacific Heights': 11
    }
}

people = [
    {'name': 'Karen', 'location': 'Pacific Heights', 'start': 1080, 'end': 1260, 'min': 90},
    {'name': 'Mark', 'location': 'Embarcadero', 'start': 570, 'end': 990, 'min': 120}
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