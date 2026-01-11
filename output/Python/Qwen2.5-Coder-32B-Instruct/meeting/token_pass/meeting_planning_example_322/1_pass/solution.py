import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    "Sunset District": {"Russian Hill": 24, "Chinatown": 30, "Presidio": 16, "Fisherman's Wharf": 29},
    "Russian Hill": {"Sunset District": 23, "Chinatown": 9, "Presidio": 14, "Fisherman's Wharf": 7},
    "Chinatown": {"Sunset District": 29, "Russian Hill": 7, "Presidio": 19, "Fisherman's Wharf": 8},
    "Presidio": {"Sunset District": 15, "Russian Hill": 14, "Chinatown": 21, "Fisherman's Wharf": 19},
    "Fisherman's Wharf": {"Sunset District": 27, "Russian Hill": 7, "Chinatown": 12, "Presidio": 17}
}

# Define meeting constraints
meetings = [
    {"location": "Russian Hill", "person": "William", "start_time": "18:30", "end_time": "20:45", "min_duration": 105},
    {"location": "Chinatown", "person": "Michelle", "start_time": "8:15", "end_time": "14:00", "min_duration": 15},
    {"location": "Presidio", "person": "George", "start_time": "10:30", "end_time": "18:45", "min_duration": 30},
    {"location": "Fisherman's Wharf", "person": "Robert", "start_time": "9:00", "end_time": "13:45", "min_duration": 30}
]

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def add_minutes_to_time(time_obj, minutes):
    return time_obj + timedelta(minutes=minutes)

def time_to_str(time_obj):
    return time_obj.strftime("%H:%M").lstrip('0')

def find_meeting_schedule(start_location, start_time):
    current_location = start_location
    current_time = parse_time(start_time)
    itinerary = []

    for meeting in meetings:
        # Calculate travel time to the next location
        travel_time = travel_times[current_location][meeting["location"]]
        
        # Calculate the earliest possible start time at the meeting location
        earliest_start_time = max(add_minutes_to_time(current_time, travel_time), parse_time(meeting["start_time"]))
        
        # Calculate the latest possible end time at the meeting location
        latest_end_time = min(add_minutes_to_time(earliest_start_time, meeting["min_duration"]), parse_time(meeting["end_time"]))
        
        # Check if the meeting can happen
        if earliest_start_time < latest_end_time:
            # Add the meeting to the itinerary
            itinerary.append({
                "action": "meet",
                "location": meeting["location"],
                "person": meeting["person"],
                "start_time": time_to_str(earliest_start_time),
                "end_time": time_to_str(latest_end_time)
            })
            
            # Update current location and time
            current_location = meeting["location"]
            current_time = latest_end_time
        else:
            # If the meeting cannot happen, skip it
            continue
    
    return itinerary

# Generate the schedule starting from Sunset District at 9:00 AM
schedule = find_meeting_schedule("Sunset District", "9:00")
result = {"itinerary": schedule}

# Output the result as a JSON-formatted string
print(json.dumps(result, indent=2))