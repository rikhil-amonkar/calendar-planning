#!/usr/bin/env python3
import json
import sys

# Convert time string "H:MM" to minutes since midnight
def time_to_minutes(time_str):
    parts = time_str.split(':')
    return int(parts[0]) * 60 + int(parts[1])

# Convert minutes since midnight to "H:MM" string (no leading zero for hour)
def minutes_to_timestr(m):
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

# Define the travel times (in minutes) as a nested dictionary
travel_times = {
    "Richmond District": {
        "Chinatown": 20,
        "Sunset District": 11,
        "Alamo Square": 13,
        "Financial District": 22,
        "North Beach": 17,
        "Embarcadero": 19,
        "Presidio": 7,
        "Golden Gate Park": 9,
        "Bayview": 27
    },
    "Chinatown": {
        "Richmond District": 20,
        "Sunset District": 29,
        "Alamo Square": 17,
        "Financial District": 5,
        "North Beach": 3,
        "Embarcadero": 5,
        "Presidio": 19,
        "Golden Gate Park": 23,
        "Bayview": 20
    },
    "Sunset District": {
        "Richmond District": 12,
        "Chinatown": 30,
        "Alamo Square": 17,
        "Financial District": 30,
        "North Beach": 28,
        "Embarcadero": 30,
        "Presidio": 16,
        "Golden Gate Park": 11,
        "Bayview": 22
    },
    "Alamo Square": {
        "Richmond District": 11,
        "Chinatown": 15,
        "Sunset District": 16,
        "Financial District": 17,
        "North Beach": 15,
        "Embarcadero": 16,
        "Presidio": 17,
        "Golden Gate Park": 9,
        "Bayview": 16
    },
    "Financial District": {
        "Richmond District": 21,
        "Chinatown": 5,
        "Sunset District": 30,
        "Alamo Square": 17,
        "North Beach": 7,
        "Embarcadero": 4,
        "Presidio": 22,
        "Golden Gate Park": 23,
        "Bayview": 19
    },
    "North Beach": {
        "Richmond District": 18,
        "Chinatown": 6,
        "Sunset District": 27,
        "Alamo Square": 16,
        "Financial District": 8,
        "Embarcadero": 6,
        "Presidio": 17,
        "Golden Gate Park": 22,
        "Bayview": 25
    },
    "Embarcadero": {
        "Richmond District": 21,
        "Chinatown": 7,
        "Sunset District": 30,
        "Alamo Square": 19,
        "Financial District": 5,
        "North Beach": 5,
        "Presidio": 20,
        "Golden Gate Park": 25,
        "Bayview": 21
    },
    "Presidio": {
        "Richmond District": 7,
        "Chinatown": 21,
        "Sunset District": 15,
        "Alamo Square": 19,
        "Financial District": 23,
        "North Beach": 18,
        "Embarcadero": 20,
        "Golden Gate Park": 12,
        "Bayview": 31
    },
    "Golden Gate Park": {
        "Richmond District": 7,
        "Chinatown": 23,
        "Sunset District": 10,
        "Alamo Square": 9,
        "Financial District": 26,
        "North Beach": 23,
        "Embarcadero": 25,
        "Presidio": 11,
        "Bayview": 23
    },
    "Bayview": {
        "Richmond District": 25,
        "Chinatown": 19,
        "Sunset District": 23,
        "Alamo Square": 16,
        "Financial District": 19,
        "North Beach": 22,
        "Embarcadero": 19,
        "Presidio": 32,
        "Golden Gate Park": 22
    }
}

# Define the meeting constraints for each friend.
# Times are stored as minutes since midnight.
meetings = [
    {"person": "Robert", "location": "Chinatown", "avail_start": 7 * 60 + 45, "avail_end": 17 * 60 + 30, "duration": 120},
    {"person": "David", "location": "Sunset District", "avail_start": 12 * 60 + 30, "avail_end": 19 * 60 + 45, "duration": 45},
    {"person": "Matthew", "location": "Alamo Square", "avail_start": 8 * 60 + 45, "avail_end": 13 * 60 + 45, "duration": 90},
    {"person": "Jessica", "location": "Financial District", "avail_start": 9 * 60 + 30, "avail_end": 18 * 60 + 45, "duration": 45},
    {"person": "Melissa", "location": "North Beach", "avail_start": 7 * 60 + 15, "avail_end": 16 * 60 + 45, "duration": 45},
    {"person": "Mark", "location": "Embarcadero", "avail_start": 15 * 60 + 15, "avail_end": 17 * 60, "duration": 45},
    {"person": "Deborah", "location": "Presidio", "avail_start": 19 * 60, "avail_end": 19 * 60 + 45, "duration": 45},
    {"person": "Karen", "location": "Golden Gate Park", "avail_start": 19 * 60 + 30, "avail_end": 22 * 60, "duration": 120},
    {"person": "Laura", "location": "Bayview", "avail_start": 21 * 60 + 15, "avail_end": 22 * 60 + 15, "duration": 15}
]

# Global best solution storage
best_itinerary = []
best_count = 0
best_end_time = sys.maxsize

def search(current_time, current_location, remaining, itinerary):
    global best_itinerary, best_count, best_end_time

    # If the current itinerary is better (more meetings) or equally good but finishes earlier,
    # update the best solution.
    if len(itinerary) > best_count or (len(itinerary) == best_count and current_time < best_end_time):
        best_itinerary = itinerary[:]
        best_count = len(itinerary)
        best_end_time = current_time

    # Try scheduling each remaining meeting in turn.
    for i, meeting in enumerate(remaining):
        # Calculate travel time from current_location to the friend's location.
        if current_location not in travel_times or meeting["location"] not in travel_times[current_location]:
            continue  # skip if unknown travel info
        travel = travel_times[current_location][meeting["location"]]
        arrival = current_time + travel
        # The meeting can start when you arrive or when the friend is available, whichever is later.
        meeting_start = max(arrival, meeting["avail_start"])
        meeting_end = meeting_start + meeting["duration"]
        # Check if meeting can finish before the friend's availability ends.
        if meeting_end <= meeting["avail_end"]:
            # Create new itinerary entry.
            new_entry = {
                "person": meeting["person"],
                "location": meeting["location"],
                "start": meeting_start,
                "end": meeting_end
            }
            # Prepare the new list of remaining meetings (remove the current one)
            new_remaining = remaining[:i] + remaining[i+1:]
            # Recurse with updated values: next current_time is meeting_end and current_location is that meeting's location.
            search(meeting_end, meeting["location"], new_remaining, itinerary + [new_entry])
    # End recursion

def main():
    # Starting conditions: You arrive at Richmond District at 9:00 (540 minutes).
    start_time = 9 * 60  # 9:00 AM in minutes
    start_location = "Richmond District"
    
    # Run the recursive search to find the optimal meeting schedule.
    search(start_time, start_location, meetings, [])

    # Prepare the output itinerary in the required JSON format.
    output_itinerary = []
    for entry in best_itinerary:
        output_itinerary.append({
            "action": "meet",
            "location": entry["location"],
            "person": entry["person"],
            "start_time": minutes_to_timestr(entry["start"]),
            "end_time": minutes_to_timestr(entry["end"])
        })
    
    result = {"itinerary": output_itinerary}
    # Output the result as JSON.
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()