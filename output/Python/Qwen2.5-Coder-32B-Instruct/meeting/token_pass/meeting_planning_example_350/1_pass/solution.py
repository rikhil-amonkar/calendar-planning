import json
from datetime import datetime, timedelta

# Constants
START_TIME = 540  # 9:00 AM in minutes
END_TIME = 1440   # 24:00 in minutes

# Travel times in minutes
travel_times = {
    ('Bayview', 'Pacific Heights'): 23,
    ('Bayview', 'Mission District'): 13,
    ('Bayview', 'Haight-Ashbury'): 19,
    ('Bayview', 'Financial District'): 19,
    ('Pacific Heights', 'Bayview'): 22,
    ('Pacific Heights', 'Mission District'): 15,
    ('Pacific Heights', 'Haight-Ashbury'): 11,
    ('Pacific Heights', 'Financial District'): 13,
    ('Mission District', 'Bayview'): 15,
    ('Mission District', 'Pacific Heights'): 16,
    ('Mission District', 'Haight-Ashbury'): 11,
    ('Mission District', 'Financial District'): 17,
    ('Haight-Ashbury', 'Bayview'): 18,
    ('Haight-Ashbury', 'Pacific Heights'): 12,
    ('Haight-Ashbury', 'Mission District'): 11,
    ('Haight-Ashbury', 'Financial District'): 21,
    ('Financial District', 'Bayview'): 19,
    ('Financial District', 'Pacific Heights'): 13,
    ('Financial District', 'Mission District'): 17,
    ('Financial District', 'Haight-Ashbury'): 19,
}

# Meeting constraints
meetings = {
    'Mary': {'location': 'Pacific Heights', 'start': 600, 'end': 1260, 'duration': 45},
    'Lisa': {'location': 'Mission District', 'start': 1350, 'end': 1440, 'duration': 75},
    'Betty': {'location': 'Haight-Ashbury', 'start': 435, 'end': 915, 'duration': 90},
    'Charles': {'location': 'Financial District', 'start': 675, 'end': 180, 'duration': 120},
}

def time_to_minutes(time_str):
    return int(datetime.strptime(time_str, '%H:%M').strftime('%H')) * 60 + int(datetime.strptime(time_str, '%H:%M').strftime('%M'))

def minutes_to_time(minutes):
    hours, minutes = divmod(minutes, 60)
    return f"{hours}:{minutes:02}"

def can_meet(current_time, meeting):
    return current_time + meeting['duration'] <= meeting['end']

def backtrack(current_location, current_time, visited, schedule):
    if len(visited) == len(meetings):
        return schedule
    
    best_schedule = None
    for person, meeting in meetings.items():
        if person not in visited:
            travel_time = travel_times.get((current_location, meeting['location']), float('inf'))
            arrival_time = current_time + travel_time
            
            if arrival_time >= meeting['start'] and can_meet(arrival_time, meeting):
                new_visited = visited | {person}
                new_schedule = schedule + [{
                    'action': 'meet',
                    'location': meeting['location'],
                    'person': person,
                    'start_time': minutes_to_time(arrival_time),
                    'end_time': minutes_to_time(arrival_time + meeting['duration'])
                }]
                
                candidate_schedule = backtrack(meeting['location'], arrival_time + meeting['duration'], new_visited, new_schedule)
                
                if candidate_schedule:
                    if not best_schedule or len(candidate_schedule) > len(best_schedule):
                        best_schedule = candidate_schedule
                        
    return best_schedule

initial_schedule = []
best_itinerary = backtrack('Bayview', START_TIME, set(), initial_schedule)

print(json.dumps({"itinerary": best_itinerary}, indent=2))