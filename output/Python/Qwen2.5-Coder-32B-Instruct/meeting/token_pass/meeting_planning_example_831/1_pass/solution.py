import json
from datetime import datetime, timedelta

# Define travel times as a graph
travel_times = {
    "Presidio": {"Fisherman's Wharf": 19, "Alamo Square": 19, "Financial District": 23, "Union Square": 22, "Sunset District": 15, "Embarcadero": 20, "Golden Gate Park": 12, "Chinatown": 21, "Richmond District": 7},
    "Fisherman's Wharf": {"Presidio": 17, "Alamo Square": 21, "Financial District": 11, "Union Square": 13, "Sunset District": 27, "Embarcadero": 8, "Golden Gate Park": 25, "Chinatown": 12, "Richmond District": 18},
    "Alamo Square": {"Presidio": 17, "Fisherman's Wharf": 19, "Financial District": 17, "Union Square": 14, "Sunset District": 16, "Embarcadero": 16, "Golden Gate Park": 9, "Chinatown": 15, "Richmond District": 11},
    "Financial District": {"Presidio": 22, "Fisherman's Wharf": 10, "Alamo Square": 17, "Union Square": 9, "Sunset District": 30, "Embarcadero": 4, "Golden Gate Park": 23, "Chinatown": 5, "Richmond District": 21},
    "Union Square": {"Presidio": 24, "Fisherman's Wharf": 15, "Alamo Square": 15, "Financial District": 9, "Sunset District": 27, "Embarcadero": 11, "Golden Gate Park": 22, "Chinatown": 7, "Richmond District": 20},
    "Sunset District": {"Presidio": 16, "Fisherman's Wharf": 29, "Alamo Square": 17, "Financial District": 30, "Union Square": 30, "Embarcadero": 30, "Golden Gate Park": 11, "Chinatown": 29, "Richmond District": 12},
    "Embarcadero": {"Presidio": 20, "Fisherman's Wharf": 6, "Alamo Square": 19, "Financial District": 5, "Union Square": 10, "Sunset District": 30, "Golden Gate Park": 25, "Chinatown": 7, "Richmond District": 21},
    "Golden Gate Park": {"Presidio": 11, "Fisherman's Wharf": 24, "Alamo Square": 9, "Financial District": 26, "Union Square": 22, "Sunset District": 10, "Embarcadero": 25, "Chinatown": 23, "Richmond District": 7},
    "Chinatown": {"Presidio": 19, "Fisherman's Wharf": 8, "Alamo Square": 17, "Financial District": 5, "Union Square": 7, "Sunset District": 29, "Embarcadero": 5, "Golden Gate Park": 23, "Richmond District": 20},
    "Richmond District": {"Presidio": 7, "Fisherman's Wharf": 18, "Alamo Square": 13, "Financial District": 22, "Union Square": 21, "Sunset District": 11, "Embarcadero": 19, "Golden Gate Park": 9, "Chinatown": 20}
}

# Define meeting constraints
meeting_constraints = {
    "Jeffrey": {"location": "Fisherman's Wharf", "start": "10:15", "end": "13:00", "duration": 90},
    "Ronald": {"location": "Alamo Square", "start": "7:45", "end": "14:45", "duration": 120},
    "Jason": {"location": "Financial District", "start": "10:45", "end": "16:00", "duration": 105},
    "Melissa": {"location": "Union Square", "start": "17:45", "end": "18:15", "duration": 15},
    "Elizabeth": {"location": "Sunset District", "start": "14:45", "end": "17:30", "duration": 105},
    "Margaret": {"location": "Embarcadero", "start": "13:15", "end": "19:00", "duration": 90},
    "George": {"location": "Golden Gate Park", "start": "19:00", "end": "22:00", "duration": 75},
    "Richard": {"location": "Chinatown", "start": "9:30", "end": "21:00", "duration": 15},
    "Laura": {"location": "Richmond District", "start": "9:45", "end": "18:00", "duration": 60}
}

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def can_meet(start, end, meeting_start, meeting_end, duration):
    meeting_start_time = parse_time(meeting_start)
    meeting_end_time = parse_time(meeting_end)
    available_duration = (meeting_end_time - meeting_start_time).total_seconds() / 60
    return start <= meeting_start_time and (end - start).total_seconds() / 60 >= duration and available_duration >= duration

def backtrack(current_location, current_time, visited_friends, itinerary):
    global best_itinerary
    
    # Check if we have a better itinerary
    if len(visited_friends) > len(best_itinerary):
        best_itinerary = itinerary.copy()
    
    # Explore next locations
    for friend, constraints in meeting_constraints.items():
        if friend not in visited_friends:
            location = constraints["location"]
            travel_time = travel_times[current_location][location]
            meeting_start = constraints["start"]
            meeting_end = constraints["end"]
            duration = constraints["duration"]
            
            new_start_time = current_time + timedelta(minutes=travel_time)
            new_end_time = new_start_time + timedelta(minutes=duration)
            
            if can_meet(new_start_time, new_end_time, meeting_start, meeting_end, duration):
                visited_friends.add(friend)
                itinerary.append({
                    "action": "meet",
                    "location": location,
                    "person": friend,
                    "start_time": new_start_time.strftime("%H:%M"),
                    "end_time": new_end_time.strftime("%H:%M")
                })
                backtrack(location, new_end_time, visited_friends, itinerary)
                itinerary.pop()
                visited_friends.remove(friend)

# Initialize variables
best_itinerary = []
initial_time = parse_time("9:00")
backtrack("Presidio", initial_time, set(), [])

# Output the best itinerary as JSON
output = {"itinerary": best_itinerary}
print(json.dumps(output, indent=2))