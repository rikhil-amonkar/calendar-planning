import json
from datetime import datetime, timedelta

# Define the travel times between locations
travel_times = {
    "Mission District": {"Alamo Square": 11, "Presidio": 25, "Russian Hill": 15, "North Beach": 17, "Golden Gate Park": 17, "Richmond District": 20, "Embarcadero": 19, "Financial District": 15, "Marina District": 19},
    "Alamo Square": {"Mission District": 10, "Presidio": 17, "Russian Hill": 13, "North Beach": 15, "Golden Gate Park": 9, "Richmond District": 11, "Embarcadero": 16, "Financial District": 17, "Marina District": 15},
    "Presidio": {"Mission District": 26, "Alamo Square": 19, "Russian Hill": 14, "North Beach": 18, "Golden Gate Park": 12, "Richmond District": 7, "Embarcadero": 20, "Financial District": 23, "Marina District": 11},
    "Russian Hill": {"Mission District": 16, "Alamo Square": 15, "Presidio": 14, "North Beach": 5, "Golden Gate Park": 21, "Richmond District": 14, "Embarcadero": 8, "Financial District": 11, "Marina District": 7},
    "North Beach": {"Mission District": 18, "Alamo Square": 16, "Presidio": 17, "Russian Hill": 4, "Golden Gate Park": 22, "Richmond District": 18, "Embarcadero": 6, "Financial District": 8, "Marina District": 9},
    "Golden Gate Park": {"Mission District": 17, "Alamo Square": 9, "Presidio": 11, "Russian Hill": 19, "North Beach": 23, "Richmond District": 7, "Embarcadero": 25, "Financial District": 26, "Marina District": 16},
    "Richmond District": {"Mission District": 20, "Alamo Square": 13, "Presidio": 7, "Russian Hill": 13, "North Beach": 17, "Golden Gate Park": 9, "Embarcadero": 19, "Financial District": 22, "Marina District": 9},
    "Embarcadero": {"Mission District": 20, "Alamo Square": 19, "Presidio": 20, "Russian Hill": 8, "North Beach": 5, "Golden Gate Park": 25, "Richmond District": 21, "Financial District": 4, "Marina District": 12},
    "Financial District": {"Mission District": 17, "Alamo Square": 17, "Presidio": 22, "Russian Hill": 11, "North Beach": 7, "Golden Gate Park": 23, "Richmond District": 21, "Embarcadero": 4, "Marina District": 15},
    "Marina District": {"Mission District": 20, "Alamo Square": 15, "Presidio": 10, "Russian Hill": 8, "North Beach": 11, "Golden Gate Park": 18, "Richmond District": 11, "Embarcadero": 14, "Financial District": 17}
}

# Define the constraints for each friend
constraints = {
    "Laura": {"location": "Alamo Square", "start": 14*60 + 30, "end": 16*60 + 15, "min_duration": 75},
    "Brian": {"location": "Presidio", "start": 10*60 + 15, "end": 17*60, "min_duration": 30},
    "Karen": {"location": "Russian Hill", "start": 18*60, "end": 20*60 + 15, "min_duration": 90},
    "Stephanie": {"location": "North Beach", "start": 10*60 + 15, "end": 16*60, "min_duration": 75},
    "Helen": {"location": "Golden Gate Park", "start": 11*60 + 30, "end": 21*60 + 45, "min_duration": 120},
    "Sandra": {"location": "Richmond District", "start": 8*60, "end": 15*60 + 15, "min_duration": 30},
    "Mary": {"location": "Embarcadero", "start": 16*60 + 45, "end": 18*60 + 45, "min_duration": 120},
    "Deborah": {"location": "Financial District", "start": 19*60, "end": 20*60 + 45, "min_duration": 105},
    "Elizabeth": {"location": "Marina District", "start": 8*60 + 30, "end": 13*60 + 15, "min_duration": 105}
}

def time_to_str(minutes):
    return str(timedelta(minutes=minutes)).split('.')[0]

def find_schedule(current_location, current_time, visited, itinerary):
    max_friends_met = len(visited)
    best_itinerary = itinerary.copy()
    
    for friend, constraint in constraints.items():
        if friend not in visited:
            location = constraint["location"]
            travel_time = travel_times[current_location][location]
            arrival_time = current_time + travel_time
            
            # Check if we can meet the friend
            if arrival_time + constraint["min_duration"] <= constraint["end"]:
                meeting_start = max(arrival_time, constraint["start"])
                meeting_end = min(meeting_start + constraint["min_duration"], constraint["end"])
                
                new_visited = visited | {friend}
                new_itinerary = itinerary + [{
                    "action": "meet",
                    "location": location,
                    "person": friend,
                    "start_time": time_to_str(meeting_start),
                    "end_time": time_to_str(meeting_end)
                }]
                
                friends_met, itinerary_found = find_schedule(location, meeting_end, new_visited, new_itinerary)
                
                if friends_met > max_friends_met:
                    max_friends_met = friends_met
                    best_itinerary = itinerary_found
    
    return max_friends_met, best_itinerary

initial_time = 9 * 60  # 9:00 AM
initial_location = "Mission District"
initial_visited = set()
initial_itinerary = []

max_friends_met, best_itinerary = find_schedule(initial_location, initial_time, initial_visited, initial_itinerary)

result = {"itinerary": best_itinerary}
print(json.dumps(result, indent=2))