#!/usr/bin/env python3
import json

def format_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

# Travel times in minutes between locations (as provided)
travel_times = {
    "Embarcadero": {
        "Bayview": 21,
        "Chinatown": 7,
        "Alamo Square": 19,
        "Nob Hill": 10,
        "Presidio": 20,
        "Union Square": 10,
        "The Castro": 25,
        "North Beach": 5,
        "Fisherman's Wharf": 6,
        "Marina District": 12,
    },
    "Bayview": {
        "Embarcadero": 19,
        "Chinatown": 19,
        "Alamo Square": 16,
        "Nob Hill": 20,
        "Presidio": 32,
        "Union Square": 18,
        "The Castro": 19,
        "North Beach": 22,
        "Fisherman's Wharf": 25,
        "Marina District": 27,
    },
    "Chinatown": {
        "Embarcadero": 5,
        "Bayview": 20,
        "Alamo Square": 17,
        "Nob Hill": 9,
        "Presidio": 19,
        "Union Square": 7,
        "The Castro": 22,
        "North Beach": 3,
        "Fisherman's Wharf": 8,
        "Marina District": 12,
    },
    "Alamo Square": {
        "Embarcadero": 16,
        "Bayview": 16,
        "Chinatown": 15,
        "Nob Hill": 11,
        "Presidio": 17,
        "Union Square": 14,
        "The Castro": 8,
        "North Beach": 15,
        "Fisherman's Wharf": 19,
        "Marina District": 15,
    },
    "Nob Hill": {
        "Embarcadero": 9,
        "Bayview": 19,
        "Chinatown": 6,
        "Alamo Square": 11,
        "Presidio": 17,
        "Union Square": 7,
        "The Castro": 17,
        "North Beach": 8,
        "Fisherman's Wharf": 10,
        "Marina District": 11,
    },
    "Presidio": {
        "Embarcadero": 20,
        "Bayview": 31,
        "Chinatown": 21,
        "Alamo Square": 19,
        "Nob Hill": 18,
        "Union Square": 22,
        "The Castro": 21,
        "North Beach": 18,
        "Fisherman's Wharf": 19,
        "Marina District": 11,
    },
    "Union Square": {
        "Embarcadero": 11,
        "Bayview": 15,
        "Chinatown": 7,
        "Alamo Square": 15,
        "Nob Hill": 9,
        "Presidio": 24,
        "The Castro": 17,
        "North Beach": 10,
        "Fisherman's Wharf": 15,
        "Marina District": 18,
    },
    "The Castro": {
        "Embarcadero": 22,
        "Bayview": 19,
        "Chinatown": 22,
        "Alamo Square": 8,
        "Nob Hill": 16,
        "Presidio": 20,
        "Union Square": 19,
        "North Beach": 20,
        "Fisherman's Wharf": 24,
        "Marina District": 21,
    },
    "North Beach": {
        "Embarcadero": 6,
        "Bayview": 25,
        "Chinatown": 6,
        "Alamo Square": 16,
        "Nob Hill": 7,
        "Presidio": 17,
        "Union Square": 7,
        "The Castro": 23,
        "Fisherman's Wharf": 5,
        "Marina District": 9,
    },
    "Fisherman's Wharf": {
        "Embarcadero": 8,
        "Bayview": 26,
        "Chinatown": 12,
        "Alamo Square": 21,
        "Nob Hill": 11,
        "Presidio": 17,
        "Union Square": 13,
        "The Castro": 27,
        "North Beach": 6,
        "Marina District": 9,
    },
    "Marina District": {
        "Embarcadero": 14,
        "Bayview": 27,
        "Chinatown": 15,
        "Alamo Square": 15,
        "Nob Hill": 12,
        "Presidio": 10,
        "Union Square": 16,
        "The Castro": 22,
        "North Beach": 11,
        "Fisherman's Wharf": 10,
    },
}

# Meeting constraints.
# Times are stored in minutes since midnight.
# For example, 9:00 AM = 540, 7:30 AM = 450, etc.
meetings = [
    {"person": "Stephanie", "location": "Presidio", "avail_start": 450, "avail_end": 615, "min_duration": 60},
    {"person": "Brian", "location": "Marina District", "avail_start": 735, "avail_end": 1080, "min_duration": 60},
    {"person": "Thomas", "location": "Fisherman's Wharf", "avail_start": 810, "avail_end": 1140, "min_duration": 30},
    {"person": "Nancy", "location": "North Beach", "avail_start": 885, "avail_end": 1200, "min_duration": 15},
    {"person": "Jessica", "location": "Nob Hill", "avail_start": 990, "avail_end": 1125, "min_duration": 120},
    {"person": "Mary", "location": "Union Square", "avail_start": 1005, "avail_end": 1290, "min_duration": 60},
    {"person": "Charles", "location": "The Castro", "avail_start": 990, "avail_end": 1320, "min_duration": 105},
    {"person": "Karen", "location": "Chinatown", "avail_start": 1155, "avail_end": 1275, "min_duration": 90},
    {"person": "Matthew", "location": "Bayview", "avail_start": 1155, "avail_end": 1320, "min_duration": 120},
    {"person": "Sarah", "location": "Alamo Square", "avail_start": 1200, "avail_end": 1305, "min_duration": 105},
]

# Global best schedule (list of meetings) found so far.
best_schedule = []

def search(current_time, current_location, remaining_meetings, itinerary):
    global best_schedule
    # Update best_schedule if this itinerary has more meetings
    if len(itinerary) > len(best_schedule):
        best_schedule = itinerary

    for i, meeting in enumerate(remaining_meetings):
        # Check if travel time is defined from current location to meeting location.
        if current_location not in travel_times or meeting["location"] not in travel_times[current_location]:
            continue

        travel_time = travel_times[current_location][meeting["location"]]
        arrival_time = current_time + travel_time
        # The meeting can start at the later of arrival or the meeting's available start
        meeting_start = max(arrival_time, meeting["avail_start"])
        meeting_end = meeting_start + meeting["min_duration"]

        # Check if we can finish the meeting before the end of the availability window.
        if meeting_end <= meeting["avail_end"]:
            new_item = {
                "person": meeting["person"],
                "location": meeting["location"],
                "start": meeting_start,
                "end": meeting_end
            }
            new_itinerary = itinerary + [new_item]
            # Remove this meeting from the list of remaining meetings.
            new_remaining = remaining_meetings[:i] + remaining_meetings[i+1:]
            search(meeting_end, meeting["location"], new_remaining, new_itinerary)

if __name__ == "__main__":
    # You arrive at Embarcadero at 9:00 AM (9*60 = 540 minutes)
    start_time = 540
    start_location = "Embarcadero"
    search(start_time, start_location, meetings, [])

    # Build JSON output with the required itinerary structure.
    output_itinerary = []
    for item in best_schedule:
        output_itinerary.append({
            "action": "meet",
            "location": item["location"],
            "person": item["person"],
            "start_time": format_time(item["start"]),
            "end_time": format_time(item["end"])
        })

    result = {"itinerary": output_itinerary}
    print(json.dumps(result))