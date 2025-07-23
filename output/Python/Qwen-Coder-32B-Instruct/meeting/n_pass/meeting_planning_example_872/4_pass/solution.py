import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    "Presidio": {"Haight-Ashbury": 15, "Nob Hill": 18, "Russian Hill": 14, "North Beach": 18, "Chinatown": 21, "Union Square": 22, "Embarcadero": 20, "Financial District": 23, "Marina District": 11},
    "Haight-Ashbury": {"Presidio": 15, "Nob Hill": 15, "Russian Hill": 17, "North Beach": 19, "Chinatown": 19, "Union Square": 19, "Embarcadero": 20, "Financial District": 21, "Marina District": 17},
    "Nob Hill": {"Presidio": 18, "Haight-Ashbury": 15, "Russian Hill": 5, "North Beach": 8, "Chinatown": 6, "Union Square": 7, "Embarcadero": 9, "Financial District": 9, "Marina District": 11},
    "Russian Hill": {"Presidio": 14, "Haight-Ashbury": 17, "Nob Hill": 5, "North Beach": 5, "Chinatown": 9, "Union Square": 10, "Embarcadero": 8, "Financial District": 11, "Marina District": 7},
    "North Beach": {"Presidio": 18, "Haight-Ashbury": 19, "Nob Hill": 8, "Russian Hill": 5, "Chinatown": 6, "Union Square": 7, "Embarcadero": 6, "Financial District": 8, "Marina District": 9},
    "Chinatown": {"Presidio": 21, "Haight-Ashbury": 19, "Nob Hill": 9, "Russian Hill": 9, "North Beach": 6, "Union Square": 7, "Embarcadero": 5, "Financial District": 5, "Marina District": 12},
    "Union Square": {"Presidio": 22, "Haight-Ashbury": 19, "Nob Hill": 7, "Russian Hill": 10, "North Beach": 7, "Chinatown": 7, "Embarcadero": 11, "Financial District": 9, "Marina District": 18},
    "Embarcadero": {"Presidio": 20, "Haight-Ashbury": 21, "Nob Hill": 9, "Russian Hill": 8, "North Beach": 6, "Chinatown": 5, "Union Square": 11, "Financial District": 4, "Marina District": 12},
    "Financial District": {"Presidio": 23, "Haight-Ashbury": 21, "Nob Hill": 9, "Russian Hill": 11, "North Beach": 8, "Chinatown": 5, "Union Square": 9, "Embarcadero": 4, "Marina District": 15},
    "Marina District": {"Presidio": 11, "Haight-Ashbury": 17, "Nob Hill": 11, "Russian Hill": 7, "North Beach": 9, "Chinatown": 12, "Union Square": 18, "Embarcadero": 12, "Financial District": 15}
}

# Define meeting constraints
constraints = {
    "Karen": {"location": "Haight-Ashbury", "start": "21:00", "end": "21:45", "min_duration": 45},
    "Jessica": {"location": "Nob Hill", "start": "13:45", "end": "21:00", "min_duration": 90},
    "Brian": {"location": "Russian Hill", "start": "15:30", "end": "21:45", "min_duration": 60},
    "Kenneth": {"location": "North Beach", "start": "9:45", "end": "21:00", "min_duration": 30},
    "Jason": {"location": "Chinatown", "start": "8:15", "end": "11:45", "min_duration": 75},
    "Stephanie": {"location": "Union Square", "start": "14:45", "end": "18:45", "min_duration": 105},
    "Kimberly": {"location": "Embarcadero", "start": "9:45", "end": "19:30", "min_duration": 75},
    "Steven": {"location": "Financial District", "start": "7:15", "end": "21:15", "min_duration": 60},
    "Mark": {"location": "Marina District", "start": "10:15", "end": "13:00", "min_duration": 75}
}

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def format_time(time_obj):
    return time_obj.strftime("%H:%M")

def can_meet(start, end, min_duration):
    duration = (parse_time(end) - parse_time(start)).total_seconds() / 60
    return duration >= min_duration

def find_schedule(constraints, travel_times):
    start_time = parse_time("9:00")
    current_location = "Presidio"
    itinerary = []

    def backtrack(current_time, current_location, visited):
        nonlocal itinerary
        if len(visited) == len(constraints):
            return True
        
        # Sort constraints by start time to prioritize earlier meetings
        sorted_constraints = sorted(constraints.items(), key=lambda x: parse_time(x[1]["start"]))
        
        for person, details in sorted_constraints:
            if person in visited:
                continue
            
            location = details["location"]
            start = details["start"]
            end = details["end"]
            min_duration = details["min_duration"]
            
            travel_time = travel_times[current_location][location]
            arrival_time = current_time + timedelta(minutes=travel_time)
            
            if arrival_time >= parse_time(end):
                continue
            
            meeting_start = max(arrival_time, parse_time(start))
            meeting_end = meeting_start + timedelta(minutes=min_duration)
            
            if meeting_end <= parse_time(end):
                itinerary.append({
                    "action": "meet",
                    "location": location,
                    "person": person,
                    "start_time": format_time(meeting_start),
                    "end_time": format_time(meeting_end)
                })
                
                if backtrack(meeting_end, location, visited | {person}):
                    return True
                
                itinerary.pop()
        
        return False

    backtrack(start_time, current_location, set())
    return itinerary

itinerary = find_schedule(constraints, travel_times)
result = {"itinerary": itinerary}
print(json.dumps(result, indent=4))