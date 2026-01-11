import json
from datetime import datetime, timedelta

# Define travel times in minutes
travel_times = {
    "Bayview": {"Embarcadero": 19, "Fisherman's Wharf": 25, "Financial District": 19},
    "Embarcadero": {"Bayview": 21, "Fisherman's Wharf": 6, "Financial District": 5},
    "Fisherman's Wharf": {"Bayview": 26, "Embarcadero": 8, "Financial District": 11},
    "Financial District": {"Bayview": 19, "Embarcadero": 4, "Fisherman's Wharf": 10}
}

# Define meeting constraints
meetings = [
    {"name": "Karen", "location": "Fisherman's Wharf", "start": "8:45", "end": "15:00", "duration": 30},
    {"name": "Anthony", "location": "Financial District", "start": "9:15", "end": "21:30", "duration": 105},
    {"name": "Betty", "location": "Embarcadero", "start": "19:45", "end": "21:45", "duration": 15}
]

# Convert times to minutes since midnight
def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

# Function to convert minutes since midnight back to time string
def minutes_to_time(minutes):
    hours = minutes // 60
    minutes = minutes % 60
    return f"{hours}:{minutes:02}"

# Main function to compute the itinerary
def compute_itinerary():
    current_time = time_to_minutes("9:00")
    current_location = "Bayview"
    itinerary = []

    # Sort meetings by their start times
    meetings.sort(key=lambda x: time_to_minutes(x["start"]))

    for meeting in meetings:
        meeting_start = time_to_minutes(meeting["start"])
        meeting_end = time_to_minutes(meeting["end"])
        required_duration = meeting["duration"]
        meeting_location = meeting["location"]
        meeting_name = meeting["name"]

        # Calculate the time needed to reach the meeting location
        travel_time = travel_times[current_location][meeting_location]
        potential_meeting_start = max(current_time + travel_time, meeting_start)

        # Check if we can fit the meeting in the available time slot
        if potential_meeting_start + required_duration <= meeting_end:
            # Schedule the meeting
            itinerary.append({
                "action": "meet",
                "location": meeting_location,
                "person": meeting_name,
                "start_time": minutes_to_time(potential_meeting_start),
                "end_time": minutes_to_time(potential_meeting_start + required_duration)
            })
            # Update current time and location
            current_time = potential_meeting_start + required_duration
            current_location = meeting_location

    return itinerary

# Compute the itinerary and print it as JSON
itinerary = compute_itinerary()
result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))