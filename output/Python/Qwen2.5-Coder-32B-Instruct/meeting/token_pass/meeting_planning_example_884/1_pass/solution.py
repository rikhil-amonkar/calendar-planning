import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    'Richmond District': {'Chinatown': 20, 'Sunset District': 11, 'Alamo Square': 13, 'Financial District': 22, 'North Beach': 17, 'Embarcadero': 19, 'Presidio': 7, 'Golden Gate Park': 9, 'Bayview': 27},
    'Chinatown': {'Richmond District': 20, 'Sunset District': 29, 'Alamo Square': 17, 'Financial District': 5, 'North Beach': 3, 'Embarcadero': 5, 'Presidio': 19, 'Golden Gate Park': 23, 'Bayview': 20},
    'Sunset District': {'Richmond District': 12, 'Chinatown': 30, 'Alamo Square': 17, 'Financial District': 30, 'North Beach': 28, 'Embarcadero': 30, 'Presidio': 16, 'Golden Gate Park': 11, 'Bayview': 22},
    'Alamo Square': {'Richmond District': 11, 'Chinatown': 15, 'Sunset District': 16, 'Financial District': 17, 'North Beach': 15, 'Embarcadero': 16, 'Presidio': 17, 'Golden Gate Park': 9, 'Bayview': 16},
    'Financial District': {'Richmond District': 21, 'Chinatown': 5, 'Sunset District': 30, 'Alamo Square': 17, 'North Beach': 7, 'Embarcadero': 4, 'Presidio': 22, 'Golden Gate Park': 23, 'Bayview': 19},
    'North Beach': {'Richmond District': 18, 'Chinatown': 6, 'Sunset District': 27, 'Alamo Square': 16, 'Financial District': 8, 'Embarcadero': 6, 'Presidio': 17, 'Golden Gate Park': 22, 'Bayview': 25},
    'Embarcadero': {'Richmond District': 21, 'Chinatown': 7, 'Sunset District': 30, 'Alamo Square': 19, 'Financial District': 5, 'North Beach': 5, 'Presidio': 20, 'Golden Gate Park': 25, 'Bayview': 21},
    'Presidio': {'Richmond District': 7, 'Chinatown': 21, 'Sunset District': 15, 'Alamo Square': 19, 'Financial District': 23, 'North Beach': 18, 'Embarcadero': 20, 'Golden Gate Park': 12, 'Bayview': 31},
    'Golden Gate Park': {'Richmond District': 7, 'Chinatown': 23, 'Sunset District': 10, 'Alamo Square': 9, 'Financial District': 26, 'North Beach': 23, 'Embarcadero': 25, 'Presidio': 11, 'Bayview': 23},
    'Bayview': {'Richmond District': 25, 'Chinatown': 19, 'Sunset District': 23, 'Alamo Square': 16, 'Financial District': 19, 'North Beach': 22, 'Embarcadero': 19, 'Presidio': 32, 'Golden Gate Park': 22}
}

# Define people's availability and meeting durations
people_constraints = {
    'Robert': {'location': 'Chinatown', 'start': '7:45', 'end': '17:30', 'duration': 120},
    'David': {'location': 'Sunset District', 'start': '12:30', 'end': '19:45', 'duration': 45},
    'Matthew': {'location': 'Alamo Square', 'start': '8:45', 'end': '13:45', 'duration': 90},
    'Jessica': {'location': 'Financial District', 'start': '9:30', 'end': '18:45', 'duration': 45},
    'Melissa': {'location': 'North Beach', 'start': '7:15', 'end': '16:45', 'duration': 45},
    'Mark': {'location': 'Embarcadero', 'start': '15:15', 'end': '17:00', 'duration': 45},
    'Deborah': {'location': 'Presidio', 'start': '19:00', 'end': '19:45', 'duration': 45},
    'Karen': {'location': 'Golden Gate Park', 'start': '19:30', 'end': '22:00', 'duration': 120},
    'Laura': {'location': 'Bayview', 'start': '21:15', 'end': '22:15', 'duration': 15}
}

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m}" if m > 9 else f"{h}:0{m}"

def find_optimal_schedule():
    start_location = 'Richmond District'
    start_time = time_to_minutes('9:00')
    
    # Initialize the best schedule
    best_schedule = []
    best_meetings = 0
    
    def dfs(current_location, current_time, visited_people, current_schedule):
        nonlocal best_schedule, best_meetings
        
        # Check if we have visited all people
        if len(visited_people) == len(people_constraints):
            if len(visited_people) > best_meetings:
                best_schedule = current_schedule[:]
                best_meetings = len(visited_people)
            return
        
        # Try to meet each person if possible
        for person, constraints in people_constraints.items():
            if person in visited_people:
                continue
            
            location = constraints['location']
            start = time_to_minutes(constraints['start'])
            end = time_to_minutes(constraints['end'])
            duration = constraints['duration']
            
            # Calculate travel time
            travel_time = travel_times[current_location][location]
            arrival_time = current_time + travel_time
            
            # Check if we can meet this person
            if start <= arrival_time <= end - duration:
                meet_start = arrival_time
                meet_end = meet_start + duration
                
                # Update schedule
                current_schedule.append({
                    "action": "meet",
                    "location": location,
                    "person": person,
                    "start_time": minutes_to_time(meet_start),
                    "end_time": minutes_to_time(meet_end)
                })
                
                # Recurse
                dfs(location, meet_end, visited_people | {person}, current_schedule)
                
                # Backtrack
                current_schedule.pop()
    
    # Start DFS
    dfs(start_location, start_time, set(), [])
    
    return best_schedule

optimal_schedule = find_optimal_schedule()

# Output the result as a JSON-formatted dictionary
result = {
    "itinerary": optimal_schedule
}

print(json.dumps(result, indent=2))