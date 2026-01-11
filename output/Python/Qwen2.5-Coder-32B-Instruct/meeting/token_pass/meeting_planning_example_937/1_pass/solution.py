import json
from datetime import datetime, timedelta

# Define the travel times as a dictionary of dictionaries
travel_times = {
    "Russian Hill": {"Sunset District": 23, "Union Square": 10, "Nob Hill": 5, "Marina District": 7, "Richmond District": 14, "Financial District": 11, "Embarcadero": 8, "The Castro": 21, "Alamo Square": 15, "Presidio": 14},
    "Sunset District": {"Russian Hill": 24, "Union Square": 30, "Nob Hill": 27, "Marina District": 21, "Richmond District": 12, "Financial District": 30, "Embarcadero": 30, "The Castro": 17, "Alamo Square": 17, "Presidio": 16},
    "Union Square": {"Russian Hill": 13, "Sunset District": 27, "Nob Hill": 9, "Marina District": 18, "Richmond District": 20, "Financial District": 9, "Embarcadero": 11, "The Castro": 17, "Alamo Square": 15, "Presidio": 24},
    "Nob Hill": {"Russian Hill": 5, "Sunset District": 24, "Union Square": 7, "Marina District": 11, "Richmond District": 14, "Financial District": 9, "Embarcadero": 9, "The Castro": 17, "Alamo Square": 11, "Presidio": 17},
    "Marina District": {"Russian Hill": 8, "Sunset District": 19, "Union Square": 16, "Nob Hill": 12, "Richmond District": 11, "Financial District": 17, "Embarcadero": 14, "The Castro": 22, "Alamo Square": 15, "Presidio": 10},
    "Richmond District": {"Russian Hill": 13, "Sunset District": 11, "Union Square": 21, "Nob Hill": 17, "Marina District": 9, "Financial District": 22, "Embarcadero": 19, "The Castro": 16, "Alamo Square": 13, "Presidio": 7},
    "Financial District": {"Russian Hill": 11, "Sunset District": 30, "Union Square": 9, "Nob Hill": 8, "Marina District": 15, "Richmond District": 21, "Embarcadero": 4, "The Castro": 20, "Alamo Square": 17, "Presidio": 22},
    "Embarcadero": {"Russian Hill": 8, "Sunset District": 30, "Union Square": 10, "Nob Hill": 10, "Marina District": 12, "Richmond District": 21, "Financial District": 5, "The Castro": 25, "Alamo Square": 19, "Presidio": 20},
    "The Castro": {"Russian Hill": 18, "Sunset District": 17, "Union Square": 19, "Nob Hill": 16, "Marina District": 21, "Richmond District": 16, "Financial District": 21, "Embarcadero": 22, "Alamo Square": 8, "Presidio": 20},
    "Alamo Square": {"Russian Hill": 13, "Sunset District": 16, "Union Square": 14, "Nob Hill": 11, "Marina District": 15, "Richmond District": 11, "Financial District": 17, "Embarcadero": 16, "The Castro": 8, "Presidio": 17},
    "Presidio": {"Russian Hill": 14, "Sunset District": 15, "Union Square": 22, "Nob Hill": 18, "Marina District": 11, "Richmond District": 7, "Financial District": 23, "Embarcadero": 20, "The Castro": 21, "Alamo Square": 19}
}

# Define the constraints as a list of dictionaries
constraints = [
    {"location": "Sunset District", "person": "David", "start_time": "9:15", "end_time": "22:00", "duration": 15},
    {"location": "Union Square", "person": "Kenneth", "start_time": "21:15", "end_time": "21:45", "duration": 15},
    {"location": "Nob Hill", "person": "Patricia", "start_time": "15:00", "end_time": "19:15", "duration": 120},
    {"location": "Marina District", "person": "Mary", "start_time": "14:45", "end_time": "16:45", "duration": 45},
    {"location": "Richmond District", "person": "Charles", "start_time": "17:15", "end_time": "21:00", "duration": 15},
    {"location": "Financial District", "person": "Joshua", "start_time": "14:30", "end_time": "17:15", "duration": 90},
    {"location": "Embarcadero", "person": "Ronald", "start_time": "18:15", "end_time": "20:45", "duration": 30},
    {"location": "The Castro", "person": "George", "start_time": "14:15", "end_time": "19:00", "duration": 105},
    {"location": "Alamo Square", "person": "Kimberly", "start_time": "9:00", "end_time": "14:30", "duration": 105},
    {"location": "Presidio", "person": "William", "start_time": "7:00", "end_time": "12:45", "duration": 60}
]

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def format_time(time_obj):
    return time_obj.strftime("%H:%M")

def can_meet(start_time, end_time, required_duration):
    return (end_time - start_time).total_seconds() / 60 >= required_duration

def find_optimal_schedule(constraints, travel_times, start_location="Russian Hill", start_time="9:00"):
    current_location = start_location
    current_time = parse_time(start_time)
    itinerary = []

    # Sort constraints by start time
    constraints.sort(key=lambda x: parse_time(x['start_time']))

    for constraint in constraints:
        location = constraint['location']
        person = constraint['person']
        required_start = parse_time(constraint['start_time'])
        required_end = parse_time(constraint['end_time'])
        required_duration = constraint['duration']

        # Calculate travel time to the location
        travel_time = travel_times[current_location][location]
        travel_duration = timedelta(minutes=travel_time)

        # Calculate the earliest possible meeting start time
        earliest_possible_start = max(current_time + travel_duration, required_start)

        # Calculate the latest possible meeting end time
        latest_possible_end = required_end

        # Calculate the actual meeting start and end times
        meeting_start = earliest_possible_start
        meeting_end = meeting_start + timedelta(minutes=required_duration)

        # Check if the meeting can be scheduled
        if can_meet(meeting_start, latest_possible_end, required_duration) and meeting_end <= parse_time("22:00"):
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": format_time(meeting_start),
                "end_time": format_time(meeting_end)
            })
            current_location = location
            current_time = meeting_end
        else:
            # If the meeting cannot be scheduled, skip it
            continue

    return itinerary

# Generate the optimal schedule
optimal_itinerary = find_optimal_schedule(constraints, travel_times)

# Output the result as a JSON-formatted dictionary
result = {
    "itinerary": optimal_itinerary
}

print(json.dumps(result, indent=2))