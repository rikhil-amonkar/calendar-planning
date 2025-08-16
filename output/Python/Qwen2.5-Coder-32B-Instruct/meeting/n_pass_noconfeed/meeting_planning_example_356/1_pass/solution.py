import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ('Bayview', 'North Beach'): 21,
    ('Bayview', 'Presidio'): 31,
    ('Bayview', 'Haight-Ashbury'): 19,
    ('Bayview', 'Union Square'): 17,
    ('North Beach', 'Bayview'): 22,
    ('North Beach', 'Presidio'): 17,
    ('North Beach', 'Haight-Ashbury'): 18,
    ('North Beach', 'Union Square'): 7,
    ('Presidio', 'Bayview'): 31,
    ('Presidio', 'North Beach'): 18,
    ('Presidio', 'Haight-Ashbury'): 15,
    ('Presidio', 'Union Square'): 22,
    ('Haight-Ashbury', 'Bayview'): 18,
    ('Haight-Ashbury', 'North Beach'): 19,
    ('Haight-Ashbury', 'Presidio'): 15,
    ('Haight-Ashbury', 'Union Square'): 17,
    ('Union Square', 'Bayview'): 15,
    ('Union Square', 'North Beach'): 10,
    ('Union Square', 'Presidio'): 24,
    ('Union Square', 'Haight-Ashbury'): 18,
}

# Define meeting constraints
meetings = {
    'Barbara': {'location': 'North Beach', 'start': '13:45', 'end': '20:15', 'min_duration': 60},
    'Margaret': {'location': 'Presidio', 'start': '10:15', 'end': '15:15', 'min_duration': 30},
    'Kevin': {'location': 'Haight-Ashbury', 'start': '20:00', 'end': '20:45', 'min_duration': 30},
    'Kimberly': {'location': 'Union Square', 'start': '7:45', 'end': '16:45', 'min_duration': 30},
}

# Start time
start_time = datetime.strptime('9:00', '%H:%M')

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def add_minutes(time, minutes):
    return time + timedelta(minutes=minutes)

def can_meet(start, end, min_duration, current_time):
    available_time = (parse_time(end) - parse_time(start)).total_seconds() / 60
    return available_time >= min_duration and current_time <= parse_time(end) - timedelta(minutes=min_duration)

def find_schedule(start_location, start_time, meetings, travel_times):
    def dfs(current_location, current_time, visited, itinerary):
        if len(visited) == len(meetings):
            return itinerary
        
        best_itinerary = None
        for person, details in meetings.items():
            if person not in visited:
                location = details['location']
                start = details['start']
                end = details['end']
                min_duration = details['min_duration']
                
                travel_time = travel_times[(current_location, location)]
                arrival_time = add_minutes(current_time, travel_time)
                
                if can_meet(start, end, min_duration, arrival_time):
                    meet_start_time = max(arrival_time, parse_time(start))
                    meet_end_time = min(add_minutes(meet_start_time, min_duration), parse_time(end))
                    
                    new_itinerary = itinerary + [{
                        "action": "meet",
                        "location": location,
                        "person": person,
                        "start_time": meet_start_time.strftime('%H:%M'),
                        "end_time": meet_end_time.strftime('%H:%M')
                    }]
                    
                    result = dfs(location, meet_end_time, visited | {person}, new_itinerary)
                    if result:
                        if not best_itinerary or len(result) > len(best_itinerary):
                            best_itinerary = result
        return best_itinerary
    
    return dfs(start_location, start_time, set(), [])

best_schedule = find_schedule('Bayview', start_time, meetings, travel_times)

print(json.dumps({"itinerary": best_schedule}))