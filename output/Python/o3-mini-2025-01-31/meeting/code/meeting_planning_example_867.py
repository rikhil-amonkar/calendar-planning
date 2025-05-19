#!/usr/bin/env python3
import json
from datetime import datetime, timedelta

# Helper functions to convert times
def str_to_time(t_str):
    # t_str in format H:MM (24hr) - assume no leading zero necessarily.
    return datetime.strptime(t_str, "%H:%M")

def time_to_str(dt):
    # Format without leading zero in hours
    return dt.strftime("%-H:%M") if hasattr(dt, 'strftime') else dt.strftime("%H:%M")

def add_minutes(dt, minutes):
    return dt + timedelta(minutes=minutes)

# Define travel times in minutes as a dictionary of dictionaries
travel_times = {
    "Haight-Ashbury": {"Mission District": 11, "Union Square": 19, "Pacific Heights": 12, "Bayview": 18, "Fisherman's Wharf": 23, "Marina District": 17, "Richmond District": 10, "Sunset District": 15, "Golden Gate Park": 7},
    "Mission District": {"Haight-Ashbury": 12, "Union Square": 15, "Pacific Heights": 16, "Bayview": 14, "Fisherman's Wharf": 22, "Marina District": 19, "Richmond District": 20, "Sunset District": 24, "Golden Gate Park": 17},
    "Union Square": {"Haight-Ashbury": 18, "Mission District": 14, "Pacific Heights": 15, "Bayview": 15, "Fisherman's Wharf": 15, "Marina District": 18, "Richmond District": 20, "Sunset District": 27, "Golden Gate Park": 22},
    "Pacific Heights": {"Haight-Ashbury": 11, "Mission District": 15, "Union Square": 12, "Bayview": 22, "Fisherman's Wharf": 13, "Marina District": 6, "Richmond District": 12, "Sunset District": 21, "Golden Gate Park": 15},
    "Bayview": {"Haight-Ashbury": 19, "Mission District": 13, "Union Square": 18, "Pacific Heights": 23, "Fisherman's Wharf": 25, "Marina District": 27, "Richmond District": 25, "Sunset District": 23, "Golden Gate Park": 22},
    "Fisherman's Wharf": {"Haight-Ashbury": 22, "Mission District": 22, "Union Square": 13, "Pacific Heights": 12, "Bayview": 26, "Marina District": 9, "Richmond District": 18, "Sunset District": 27, "Golden Gate Park": 25},
    "Marina District": {"Haight-Ashbury": 16, "Mission District": 20, "Union Square": 16, "Pacific Heights": 7, "Bayview": 27, "Fisherman's Wharf": 10, "Richmond District": 11, "Sunset District": 19, "Golden Gate Park": 18},
    "Richmond District": {"Haight-Ashbury": 10, "Mission District": 20, "Union Square": 21, "Pacific Heights": 10, "Bayview": 27, "Fisherman's Wharf": 18, "Marina District": 9, "Sunset District": 11, "Golden Gate Park": 9},
    "Sunset District": {"Haight-Ashbury": 15, "Mission District": 25, "Union Square": 30, "Pacific Heights": 21, "Bayview": 22, "Fisherman's Wharf": 29, "Marina District": 21, "Richmond District": 12, "Golden Gate Park": 11},
    "Golden Gate Park": {"Haight-Ashbury": 7, "Mission District": 17, "Union Square": 22, "Pacific Heights": 16, "Bayview": 23, "Fisherman's Wharf": 24, "Marina District": 16, "Richmond District": 7, "Sunset District": 10}
}

# Friends meeting constraints as a list in the planned meeting order.
# Order determined by manual planning to maximize meeting as many friends as possible.
# Each meeting: person, location, available start, available end, minimum meeting duration (in minutes)
meetings = [
    {"person": "Sandra", "location": "Pacific Heights", "avail_start": "7:00",    "avail_end": "20:00", "min_duration": 120},
    {"person": "Kenneth", "location": "Marina District", "avail_start": "10:45", "avail_end": "13:00", "min_duration": 45},
    {"person": "Amanda",  "location": "Golden Gate Park", "avail_start": "7:45",  "avail_end": "18:45", "min_duration": 15},
    {"person": "Elizabeth", "location": "Mission District", "avail_start": "10:30", "avail_end": "20:00", "min_duration": 90},
    {"person": "Robert", "location": "Fisherman's Wharf", "avail_start": "10:00", "avail_end": "15:00", "min_duration": 15},
    {"person": "David", "location": "Union Square", "avail_start": "15:15", "avail_end": "19:00", "min_duration": 45},
    {"person": "Kimberly", "location": "Sunset District", "avail_start": "10:15", "avail_end": "18:15", "min_duration": 105},
    {"person": "Melissa", "location": "Richmond District", "avail_start": "18:15", "avail_end": "20:00", "min_duration": 15},
    {"person": "Thomas", "location": "Bayview", "avail_start": "19:30", "avail_end": "20:30", "min_duration": 30},
]

# Starting parameters
start_location = "Haight-Ashbury"
start_time_str = "9:00"
current_time = str_to_time(start_time_str)
current_location = start_location

itinerary = []

# Function to get travel time between two locations
def get_travel_time(orig, dest):
    if orig == dest:
        return 0
    return travel_times.get(orig, {}).get(dest, 9999)

# Process each meeting in sequence
for meeting in meetings:
    # Calculate travel time
    travel_time = get_travel_time(current_location, meeting["location"])
    # Depart current_time and add travel
    current_time = add_minutes(current_time, travel_time)
    
    # The meeting can only start at the later of arrival and the person's available start time
    meeting_avail_start = str_to_time(meeting["avail_start"])
    if current_time < meeting_avail_start:
        current_time = meeting_avail_start  # wait until available
    meeting_start = current_time
    
    # Compute meeting end time by adding minimum meeting duration
    meeting_end = add_minutes(meeting_start, meeting["min_duration"])
    
    # Check if meeting end time is within the person's availability window; if not, skip or adjust.
    meeting_avail_end = str_to_time(meeting["avail_end"])
    if meeting_end > meeting_avail_end:
        # If we cannot meet the minimum duration, then skip meeting (or adjust, here we skip)
        continue

    # Add meeting to itinerary
    itinerary.append({
        "action": "meet",
        "location": meeting["location"],
        "person": meeting["person"],
        "start_time": time_to_str(meeting_start),
        "end_time": time_to_str(meeting_end)
    })
    
    # Update current_time and current_location
    current_time = meeting_end
    current_location = meeting["location"]

# Output the itinerary as JSON
output = {"itinerary": itinerary}
print(json.dumps(output, indent=2))