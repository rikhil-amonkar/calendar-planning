import json
from datetime import datetime, timedelta

# Define the travel times as a dictionary of dictionaries
travel_times = {
    "Marina District": {"Richmond District": 11, "Union Square": 16, "Nob Hill": 12, "Fisherman's Wharf": 10, "Golden Gate Park": 18, "Embarcadero": 14, "Financial District": 17, "North Beach": 11, "Presidio": 10},
    "Richmond District": {"Marina District": 9, "Union Square": 21, "Nob Hill": 17, "Fisherman's Wharf": 18, "Golden Gate Park": 9, "Embarcadero": 19, "Financial District": 22, "North Beach": 17, "Presidio": 7},
    "Union Square": {"Marina District": 18, "Richmond District": 20, "Nob Hill": 9, "Fisherman's Wharf": 15, "Golden Gate Park": 22, "Embarcadero": 11, "Financial District": 9, "North Beach": 10, "Presidio": 24},
    "Nob Hill": {"Marina District": 11, "Richmond District": 14, "Union Square": 7, "Fisherman's Wharf": 10, "Golden Gate Park": 17, "Embarcadero": 9, "Financial District": 9, "North Beach": 8, "Presidio": 17},
    "Fisherman's Wharf": {"Marina District": 9, "Richmond District": 18, "Union Square": 13, "Nob Hill": 11, "Golden Gate Park": 25, "Embarcadero": 8, "Financial District": 11, "North Beach": 6, "Presidio": 17},
    "Golden Gate Park": {"Marina District": 16, "Richmond District": 7, "Union Square": 22, "Nob Hill": 20, "Fisherman's Wharf": 24, "Embarcadero": 25, "Financial District": 26, "North Beach": 23, "Presidio": 11},
    "Embarcadero": {"Marina District": 12, "Richmond District": 21, "Union Square": 10, "Nob Hill": 10, "Fisherman's Wharf": 6, "Golden Gate Park": 25, "Financial District": 5, "North Beach": 6, "Presidio": 20},
    "Financial District": {"Marina District": 15, "Richmond District": 21, "Union Square": 9, "Nob Hill": 8, "Fisherman's Wharf": 10, "Golden Gate Park": 23, "Embarcadero": 4, "North Beach": 7, "Presidio": 22},
    "North Beach": {"Marina District": 9, "Richmond District": 18, "Union Square": 7, "Nob Hill": 7, "Fisherman's Wharf": 5, "Golden Gate Park": 22, "Embarcadero": 6, "Financial District": 8, "Presidio": 17},
    "Presidio": {"Marina District": 11, "Richmond District": 7, "Union Square": 22, "Nob Hill": 18, "Fisherman's Wharf": 19, "Golden Gate Park": 12, "Embarcadero": 20, "Financial District": 23, "North Beach": 18}
}

# Define the meeting constraints
constraints = {
    "Stephanie": {"location": "Richmond District", "start_time": "16:15", "end_time": "21:30", "min_duration": 75},
    "William": {"location": "Union Square", "start_time": "10:45", "end_time": "17:30", "min_duration": 45},
    "Elizabeth": {"location": "Nob Hill", "start_time": "12:15", "end_time": "15:00", "min_duration": 105},
    "Joseph": {"location": "Fisherman's Wharf", "start_time": "12:45", "end_time": "14:00", "min_duration": 75},
    "Anthony": {"location": "Golden Gate Park", "start_time": "13:00", "end_time": "20:30", "min_duration": 75},
    "Barbara": {"location": "Embarcadero", "start_time": "19:15", "end_time": "20:30", "min_duration": 75},
    "Carol": {"location": "Financial District", "start_time": "11:45", "end_time": "16:15", "min_duration": 60},
    "Sandra": {"location": "North Beach", "start_time": "10:00", "end_time": "12:30", "min_duration": 15},
    "Kenneth": {"location": "Presidio", "start_time": "21:15", "end_time": "22:15", "min_duration": 45}
}

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02}"

def find_meeting_schedule(constraints, travel_times):
    current_location = "Marina District"
    current_time = time_to_minutes("9:00")
    itinerary = []

    # Sort constraints by start time
    sorted_constraints = sorted(constraints.items(), key=lambda x: time_to_minutes(x[1]['start_time']))

    for name, details in sorted_constraints:
        location = details['location']
        start_time = time_to_minutes(details['start_time'])
        end_time = time_to_minutes(details['end_time'])
        min_duration = details['min_duration']

        # Calculate travel time to the next location
        travel_time = travel_times[current_location][location]

        # Check if we can reach the location in time
        if current_time + travel_time > start_time:
            continue

        # Calculate the available meeting time
        available_start_time = max(current_time + travel_time, start_time)
        available_end_time = min(available_start_time + min_duration, end_time)

        # If the available meeting time is less than the required duration, skip
        if available_end_time - available_start_time < min_duration:
            continue

        # Add the meeting to the itinerary
        itinerary.append({
            "action": "meet",
            "location": location,
            "person": name,
            "start_time": minutes_to_time(available_start_time),
            "end_time": minutes_to_time(available_end_time)
        })

        # Update the current location and time
        current_location = location
        current_time = available_end_time

    return itinerary

itinerary = find_meeting_schedule(constraints, travel_times)
result = {"itinerary": itinerary}
print(json.dumps(result))