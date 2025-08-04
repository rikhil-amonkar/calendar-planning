import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ('Bayview', 'Embarcadero'): 19,
    ('Bayview', 'Fisherman\'s Wharf'): 25,
    ('Bayview', 'Financial District'): 19,
    ('Embarcadero', 'Bayview'): 21,
    ('Embarcadero', 'Fisherman\'s Wharf'): 6,
    ('Embarcadero', 'Financial District'): 5,
    ('Fisherman\'s Wharf', 'Bayview'): 26,
    ('Fisherman\'s Wharf', 'Embarcadero'): 8,
    ('Fisherman\'s Wharf', 'Financial District'): 11,
    ('Financial District', 'Bayview'): 19,
    ('Financial District', 'Embarcadero'): 4,
    ('Financial District', 'Fisherman\'s Wharf'): 10,
}

# Define meeting constraints
constraints = {
    'Betty': {'location': 'Embarcadero', 'start': '19:45', 'end': '21:45', 'min_duration': 15},
    'Karen': {'location': 'Fisherman\'s Wharf', 'start': '8:45', 'end': '15:00', 'min_duration': 30},
    'Anthony': {'location': 'Financial District', 'start': '9:15', 'end': '21:30', 'min_duration': 105},
}

# Start time
start_time = datetime.strptime('9:00', '%H:%M')

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def format_time(dt):
    return dt.strftime('%H:%M').lstrip('0')

def find_meeting_schedule(start_time, constraints, travel_times):
    def can_meet(start, end, min_duration):
        duration = (parse_time(end) - parse_time(start)).total_seconds() / 60
        return duration >= min_duration

    def add_travel_time(current_location, next_location, current_time):
        travel_time = travel_times[(current_location, next_location)]
        return current_time + timedelta(minutes=travel_time)

    def backtrack(current_location, current_time, visited, itinerary):
        if len(visited) == len(constraints):
            return itinerary

        best_itinerary = None
        for person, details in constraints.items():
            if person in visited:
                continue
            location = details['location']
            start = details['start']
            end = details['end']
            min_duration = details['min_duration']

            # Calculate potential meeting start and end times
            travel_to_location = add_travel_time(current_location, location, current_time)
            meeting_start = max(travel_to_location, parse_time(start))
            meeting_end = min(parse_time(end), meeting_start + timedelta(minutes=min_duration))

            if can_meet(format_time(meeting_start), format_time(meeting_end), min_duration):
                new_visited = visited | {person}
                new_itinerary = itinerary + [{
                    "action": "meet",
                    "location": location,
                    "person": person,
                    "start_time": format_time(meeting_start),
                    "end_time": format_time(meeting_end)
                }]
                result = backtrack(location, meeting_end, new_visited, new_itinerary)
                if result:
                    if not best_itinerary or (best_itinerary and len(result) > len(best_itinerary)):
                        best_itinerary = result
        return best_itinerary

    return backtrack('Bayview', start_time, set(), [])

itinerary = find_meeting_schedule(start_time, constraints, travel_times)
result = {"itinerary": itinerary}
print(json.dumps(result))