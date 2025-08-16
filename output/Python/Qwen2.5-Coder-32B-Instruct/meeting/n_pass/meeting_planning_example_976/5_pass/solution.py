import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    "Embarcadero": {"Bayview": 21, "Chinatown": 7, "Alamo Square": 19, "Nob Hill": 10, "Presidio": 20, "Union Square": 10, "The Castro": 25, "North Beach": 5, "Fisherman's Wharf": 6, "Marina District": 12},
    "Bayview": {"Embarcadero": 19, "Chinatown": 19, "Alamo Square": 16, "Nob Hill": 20, "Presidio": 32, "Union Square": 18, "The Castro": 19, "North Beach": 22, "Fisherman's Wharf": 25, "Marina District": 27},
    "Chinatown": {"Embarcadero": 5, "Bayview": 20, "Alamo Square": 17, "Nob Hill": 9, "Presidio": 19, "Union Square": 7, "The Castro": 22, "North Beach": 3, "Fisherman's Wharf": 8, "Marina District": 12},
    "Alamo Square": {"Embarcadero": 16, "Bayview": 16, "Chinatown": 15, "Nob Hill": 11, "Presidio": 17, "Union Square": 14, "The Castro": 8, "North Beach": 15, "Fisherman's Wharf": 19, "Marina District": 15},
    "Nob Hill": {"Embarcadero": 9, "Bayview": 19, "Chinatown": 6, "Alamo Square": 11, "Presidio": 17, "Union Square": 7, "The Castro": 17, "North Beach": 8, "Fisherman's Wharf": 10, "Marina District": 11},
    "Presidio": {"Embarcadero": 20, "Bayview": 31, "Chinatown": 21, "Alamo Square": 19, "Nob Hill": 18, "Union Square": 22, "The Castro": 21, "North Beach": 18, "Fisherman's Wharf": 19, "Marina District": 11},
    "Union Square": {"Embarcadero": 11, "Bayview": 15, "Chinatown": 7, "Alamo Square": 15, "Nob Hill": 9, "Presidio": 24, "The Castro": 17, "North Beach": 7, "Fisherman's Wharf": 15, "Marina District": 18},
    "The Castro": {"Embarcadero": 22, "Bayview": 19, "Chinatown": 22, "Alamo Square": 8, "Nob Hill": 16, "Presidio": 20, "Union Square": 19, "North Beach": 20, "Fisherman's Wharf": 27, "Marina District": 21},
    "North Beach": {"Embarcadero": 6, "Bayview": 25, "Chinatown": 3, "Alamo Square": 16, "Nob Hill": 7, "Presidio": 17, "Union Square": 7, "The Castro": 23, "Fisherman's Wharf": 5, "Marina District": 9},
    "Fisherman's Wharf": {"Embarcadero": 8, "Bayview": 26, "Chinatown": 12, "Alamo Square": 21, "Nob Hill": 11, "Presidio": 17, "Union Square": 13, "The Castro": 27, "North Beach": 5, "Marina District": 10},
    "Marina District": {"Embarcadero": 14, "Bayview": 27, "Chinatown": 15, "Alamo Square": 15, "Nob Hill": 12, "Presidio": 10, "Union Square": 16, "The Castro": 22, "North Beach": 11, "Fisherman's Wharf": 10}
}

# Define meeting constraints
meetings = {
    "Matthew": {"location": "Bayview", "start": "19:15", "end": "22:00", "min_duration": 120},
    "Karen": {"location": "Chinatown", "start": "19:15", "end": "21:15", "min_duration": 90},
    "Sarah": {"location": "Alamo Square", "start": "20:00", "end": "21:45", "min_duration": 105},
    "Jessica": {"location": "Nob Hill", "start": "16:30", "end": "18:45", "min_duration": 120},
    "Stephanie": {"location": "Presidio", "start": "07:30", "end": "10:15", "min_duration": 60},
    "Mary": {"location": "Union Square", "start": "16:45", "end": "21:30", "min_duration": 60},
    "Charles": {"location": "The Castro", "start": "16:30", "end": "22:00", "min_duration": 105},
    "Nancy": {"location": "North Beach", "start": "14:45", "end": "20:00", "min_duration": 15},
    "Thomas": {"location": "Fisherman's Wharf", "start": "13:30", "end": "19:00", "min_duration": 30},
    "Brian": {"location": "Marina District", "start": "12:15", "end": "18:00", "min_duration": 60}
}

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def format_time(time_obj):
    return time_obj.strftime("%H:%M")

def find_schedule(start_location, start_time, meetings, travel_times):
    def can_meet(person, current_time):
        meeting = meetings[person]
        start = parse_time(meeting["start"])
        end = parse_time(meeting["end"])
        min_duration = meeting["min_duration"]
        if current_time + timedelta(minutes=min_duration) <= end and current_time >= start:
            return True, start, end
        return False, None, None

    def dfs(current_location, current_time, visited, itinerary):
        nonlocal best_itinerary
        if len(itinerary) > len(best_itinerary):
            best_itinerary = itinerary[:]
        for person, meeting in meetings.items():
            if person not in visited:
                location = meeting["location"]
                travel_time = travel_times[current_location][location]
                arrival_time = current_time + timedelta(minutes=travel_time)
                can, start, end = can_meet(person, arrival_time)
                if can:
                    leave_time = start + timedelta(minutes=meeting["min_duration"])
                    new_itinerary = itinerary + [{
                        "action": "travel",
                        "from": current_location,
                        "to": location,
                        "start_time": format_time(current_time),
                        "end_time": format_time(arrival_time)
                    }, {
                        "action": "meet",
                        "location": location,
                        "person": person,
                        "start_time": format_time(start),
                        "end_time": format_time(leave_time)
                    }]
                    dfs(location, leave_time, visited | {person}, new_itinerary)

    best_itinerary = []
    dfs(start_location, parse_time(start_time), set(), [])
    return best_itinerary

start_location = "Embarcadero"
start_time = "09:00"
optimal_schedule = find_schedule(start_location, start_time, meetings, travel_times)

print(json.dumps({"itinerary": optimal_schedule}, indent=2))