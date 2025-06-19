import json
from datetime import datetime, timedelta

def calculate_travel_time(start, end, travel_times):
    locations = list(travel_times.keys())
    start_index = locations.index(start)
    end_index = locations.index(end)
    travel_time = 0
    for i in range(start_index, end_index):
        travel_time += travel_times[locations[i]]
    return travel_time

def find_optimal_schedule(arrival_time, constraints):
    travel_times = {
        "Embarcadero": {
            "Presidio": 20,
            "Richmond District": 21,
            "Fisherman's Wharf": 6
        },
        "Presidio": {
            "Embarcadero": 20,
            "Richmond District": 7,
            "Fisherman's Wharf": 19
        },
        "Richmond District": {
            "Embarcadero": 19,
            "Presidio": 7,
            "Fisherman's Wharf": 18
        },
        "Fisherman's Wharf": {
            "Embarcadero": 8,
            "Presidio": 17,
            "Richmond District": 18
        }
    }

    schedule = []
    current_time = arrival_time

    for person, time_range in constraints.items():
        location = time_range['location']
        start_time = datetime.strptime(time_range['start_time'], '%H:%M')
        end_time = datetime.strptime(time_range['end_time'], '%H:%M')
        if current_time < start_time:
            travel_time = calculate_travel_time('Embarcadero', location, travel_times)
            current_time += timedelta(minutes=travel_time)
            schedule.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": current_time.strftime('%H:%M'),
                "end_time": (current_time + timedelta(minutes=time_range['duration'])).strftime('%H:%M')
            })
            current_time += timedelta(minutes=time_range['duration'])
        elif current_time > end_time:
            continue
        else:
            travel_time = calculate_travel_time(location, 'Embarcadero', travel_times)
            current_time += timedelta(minutes=travel_time)
            schedule.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": current_time.strftime('%H:%M'),
                "end_time": (current_time + timedelta(minutes=time_range['duration'])).strftime('%H:%M')
            })
            current_time += timedelta(minutes=time_range['duration'])

    return schedule

def main():
    arrival_time = '09:00'
    constraints = {
        'Betty': {'location': 'Presidio','start_time': '10:15', 'end_time': '21:30', 'duration': 45},
        'David': {'location': 'Richmond District','start_time': '13:00', 'end_time': '20:15', 'duration': 90},
        'Barbara': {'location': 'Fisherman\'s Wharf','start_time': '09:15', 'end_time': '20:15', 'duration': 120}
    }
    schedule = find_optimal_schedule(arrival_time, constraints)
    print('SOLUTION:')
    print(json.dumps({'itinerary': schedule}, indent=4))

if __name__ == "__main__":
    main()