import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ('Bayview', 'Embarcadero'): 19,
    ('Bayview', 'Richmond District'): 25,
    ('Bayview', 'Fisherman\'s Wharf'): 25,
    ('Embarcadero', 'Bayview'): 21,
    ('Embarcadero', 'Richmond District'): 21,
    ('Embarcadero', 'Fisherman\'s Wharf'): 6,
    ('Richmond District', 'Bayview'): 26,
    ('Richmond District', 'Embarcadero'): 19,
    ('Richmond District', 'Fisherman\'s Wharf'): 18,
    ('Fisherman\'s Wharf', 'Bayview'): 26,
    ('Fisherman\'s Wharf', 'Embarcadero'): 8,
    ('Fisherman\'s Wharf', 'Richmond District'): 18
}

# Define meeting constraints
meetings = [
    {'name': 'Jessica', 'location': 'Embarcadero', 'start': '16:45', 'end': '19:00', 'duration': 30},
    {'name': 'Sandra', 'location': 'Richmond District', 'start': '18:30', 'end': '21:45', 'duration': 120},
    {'name': 'Jason', 'location': 'Fisherman\'s Wharf', 'start': '16:00', 'end': '16:45', 'duration': 30}
]

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def add_minutes(time, minutes):
    return time + timedelta(minutes=minutes)

def time_to_str(time):
    return time.strftime('%H:%M')

def find_optimal_schedule(start_location='Bayview', start_time='9:00'):
    start_time = parse_time(start_time)
    best_itinerary = []
    max_meetings = 0

    def dfs(current_location, current_time, visited, itinerary):
        nonlocal best_itinerary, max_meetings
        # Check if we can meet any new people
        for meeting in meetings:
            if meeting['name'] not in visited:
                meeting_start = parse_time(meeting['start'])
                meeting_end = parse_time(meeting['end'])
                required_duration = meeting['duration']
                required_end = add_minutes(current_time, travel_times[(current_location, meeting['location'])] + required_duration)
                
                # Check if we can reach and meet within the meeting's window
                if current_time <= meeting_start and required_end <= meeting_end:
                    new_itinerary = itinerary + [{
                        "action": "meet",
                        "location": meeting['location'],
                        "person": meeting['name'],
                        "start_time": time_to_str(add_minutes(current_time, travel_times[(current_location, meeting['location'])])),
                        "end_time": time_to_str(required_end)
                    }]
                    new_visited = visited | {meeting['name']}
                    
                    # Continue DFS from the new location
                    dfs(meeting['location'], required_end, new_visited, new_itinerary)
        
        # If no more meetings can be scheduled, check if this is the best itinerary
        if len(itinerary) > max_meetings:
            best_itinerary = itinerary
            max_meetings = len(itinerary)

    dfs(start_location, start_time, set(), [])
    
    return best_itinerary

optimal_itinerary = find_optimal_schedule()
result = {"itinerary": optimal_itinerary}
print(json.dumps(result, indent=2))