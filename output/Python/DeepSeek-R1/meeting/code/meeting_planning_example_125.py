import json

def min_to_time(mins):
    hours = mins // 60
    minutes = mins % 60
    return f"{hours}:{minutes:02d}"

travel_time = {
    'Embarcadero': {'Financial District': 5, 'Alamo Square': 19},
    'Financial District': {'Embarcadero': 4, 'Alamo Square': 17},
    'Alamo Square': {'Embarcadero': 17, 'Financial District': 17}
}

people = {
    'Stephanie': {
        'location': 'Financial District',
        'available_start': 8 * 60 + 15,
        'available_end': 11 * 60 + 30,
        'min_duration': 90
    },
    'John': {
        'location': 'Alamo Square',
        'available_start': 10 * 60 + 15,
        'available_end': 20 * 60 + 45,
        'min_duration': 30
    }
}

orders = [['Stephanie', 'John'], ['John', 'Stephanie']]
best = None

for order in orders:
    current_time = 9 * 60
    current_loc = 'Embarcadero'
    itinerary = []
    valid = True
    
    for name in order:
        p = people[name]
        dest = p['location']
        tt = travel_time[current_loc].get(dest, None)
        if tt is None:
            valid = False
            break
        arrive = current_time + tt
        start = max(arrive, p['available_start'])
        if start + p['min_duration'] > p['available_end']:
            valid = False
            break
        end = start + p['min_duration']
        itinerary.append((current_loc, dest, name, start, end))
        current_time = end
        current_loc = dest
    
    if valid:
        best = [{
            "action": "meet",
            "location": dest,
            "person": name,
            "start_time": min_to_time(start),
            "end_time": min_to_time(end)
        } for (_, dest, name, start, end) in itinerary]
        break

print(json.dumps({"itinerary": best} if best else {"itinerary": []}))