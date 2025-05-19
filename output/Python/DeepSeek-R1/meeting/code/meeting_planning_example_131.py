import json

def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

travel_times = {
    'Pacific Heights': {'Presidio': 11, 'Marina District': 6},
    'Presidio': {'Pacific Heights': 11, 'Marina District': 10},
    'Marina District': {'Pacific Heights': 7, 'Presidio': 10}
}

itinerary = []
current_time = 9 * 60  # 9:00 AM
current_loc = 'Pacific Heights'

# Meet Jason first
travel_time = travel_times[current_loc]['Presidio']
arrival = current_time + travel_time
jason_start = max(arrival, 10 * 60)
jason_end = jason_start + 90

if jason_end <= 16 * 60 + 15:
    itinerary.append({
        "action": "meet",
        "location": "Presidio",
        "person": "Jason",
        "start_time": format_time(jason_start),
        "end_time": format_time(jason_end)
    })
    current_time = jason_end
    current_loc = 'Presidio'

    # Travel to Marina
    travel_time = travel_times[current_loc]['Marina District']
    arrival = current_time + travel_time
    kenneth_start = max(arrival, 15 * 60 + 30)
    kenneth_end = min(kenneth_start + 45, 16 * 60 + 45)

    if kenneth_end - kenneth_start >= 45:
        itinerary.append({
            "action": "meet",
            "location": "Marina District",
            "person": "Kenneth",
            "start_time": format_time(kenneth_start),
            "end_time": format_time(kenneth_end)
        })

print(json.dumps({"itinerary": itinerary}, indent=2))