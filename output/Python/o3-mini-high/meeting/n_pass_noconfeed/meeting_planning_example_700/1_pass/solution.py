#!/usr/bin/env python3
import json

# Helper function to convert minutes since midnight to "H:MM" string (24-hour format)
def format_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

# Travel times between locations (in minutes)
travel_times = {
    "Presidio": {
        "Pacific Heights": 11,
        "Golden Gate Park": 12,
        "Fisherman's Wharf": 19,
        "Marina District": 11,
        "Alamo Square": 19,
        "Sunset District": 15,
        "Nob Hill": 18,
        "North Beach": 18
    },
    "Pacific Heights": {
        "Presidio": 11,
        "Golden Gate Park": 15,
        "Fisherman's Wharf": 13,
        "Marina District": 6,
        "Alamo Square": 10,
        "Sunset District": 21,
        "Nob Hill": 8,
        "North Beach": 9
    },
    "Golden Gate Park": {
        "Presidio": 11,
        "Pacific Heights": 16,
        "Fisherman's Wharf": 24,
        "Marina District": 16,
        "Alamo Square": 9,
        "Sunset District": 10,
        "Nob Hill": 20,
        "North Beach": 23
    },
    "Fisherman's Wharf": {
        "Presidio": 17,
        "Pacific Heights": 12,
        "Golden Gate Park": 25,
        "Marina District": 9,
        "Alamo Square": 21,
        "Sunset District": 27,
        "Nob Hill": 11,
        "North Beach": 6
    },
    "Marina District": {
        "Presidio": 10,
        "Pacific Heights": 7,
        "Golden Gate Park": 18,
        "Fisherman's Wharf": 10,
        "Alamo Square": 15,
        "Sunset District": 19,
        "Nob Hill": 12,
        "North Beach": 11
    },
    "Alamo Square": {
        "Presidio": 17,
        "Pacific Heights": 10,
        "Golden Gate Park": 9,
        "Fisherman's Wharf": 19,
        "Marina District": 15,
        "Sunset District": 16,
        "Nob Hill": 11,
        "North Beach": 15
    },
    "Sunset District": {
        "Presidio": 16,
        "Pacific Heights": 21,
        "Golden Gate Park": 11,
        "Fisherman's Wharf": 29,
        "Marina District": 21,
        "Alamo Square": 17,
        "Nob Hill": 27,
        "North Beach": 28
    },
    "Nob Hill": {
        "Presidio": 17,
        "Pacific Heights": 8,
        "Golden Gate Park": 17,
        "Fisherman's Wharf": 10,
        "Marina District": 11,
        "Alamo Square": 11,
        "Sunset District": 24,
        "North Beach": 8
    },
    "North Beach": {
        "Presidio": 17,
        "Pacific Heights": 8,
        "Golden Gate Park": 22,
        "Fisherman's Wharf": 5,
        "Marina District": 9,
        "Alamo Square": 16,
        "Sunset District": 27,
        "Nob Hill": 7
    }
}

# Meeting constraint definitions.
# Times are stored in minutes from midnight.
friends = [
    {
        "person": "Kevin",
        "location": "Pacific Heights",
        "avail_start": 7 * 60 + 15,   # 7:15
        "avail_end": 8 * 60 + 45,       # 8:45
        "duration": 90
    },
    {
        "person": "Michelle",
        "location": "Golden Gate Park",
        "avail_start": 20 * 60 + 0,     # 20:00
        "avail_end": 21 * 60 + 0,       # 21:00
        "duration": 15
    },
    {
        "person": "Emily",
        "location": "Fisherman's Wharf",
        "avail_start": 16 * 60 + 15,    # 16:15
        "avail_end": 19 * 60 + 0,       # 19:00
        "duration": 30
    },
    {
        "person": "Mark",
        "location": "Marina District",
        "avail_start": 18 * 60 + 15,    # 18:15
        "avail_end": 19 * 60 + 45,      # 19:45
        "duration": 75
    },
    {
        "person": "Barbara",
        "location": "Alamo Square",
        "avail_start": 17 * 60 + 0,     # 17:00
        "avail_end": 19 * 60 + 0,       # 19:00
        "duration": 120
    },
    {
        "person": "Laura",
        "location": "Sunset District",
        "avail_start": 19 * 60 + 0,     # 19:00
        "avail_end": 21 * 60 + 15,      # 21:15
        "duration": 75
    },
    {
        "person": "Mary",
        "location": "Nob Hill",
        "avail_start": 17 * 60 + 30,    # 17:30
        "avail_end": 19 * 60 + 0,       # 19:00
        "duration": 45
    },
    {
        "person": "Helen",
        "location": "North Beach",
        "avail_start": 11 * 60 + 0,     # 11:00
        "avail_end": 12 * 60 + 15,      # 12:15
        "duration": 45
    }
]

# Recursive backtracking search to build a feasible meeting itinerary.
def search(current_time, current_location, remaining_friends, current_schedule):
    best_schedule = current_schedule[:]  # Start with current schedule as best.
    # Try each friend as the next meeting (order matters)
    for i, friend in enumerate(remaining_friends):
        # Compute travel time from the current location to the friend's location.
        if current_location not in travel_times or friend["location"] not in travel_times[current_location]:
            continue  # Skip if no travel time is defined.
        travel = travel_times[current_location][friend["location"]]
        arrival_time = current_time + travel
        # The meeting can start only when you arrive and when the friend's availability begins.
        meeting_start = max(arrival_time, friend["avail_start"])
        meeting_end = meeting_start + friend["duration"]
        # Check if meeting can finish before friend's availability ends.
        if meeting_end <= friend["avail_end"]:
            meeting_info = {
                "action": "meet",
                "location": friend["location"],
                "person": friend["person"],
                "start_time": meeting_start,
                "end_time": meeting_end
            }
            # Build the next schedule by adding this meeting.
            new_schedule = current_schedule + [meeting_info]
            # Remove the scheduled friend from remaining list.
            new_remaining = remaining_friends[:i] + remaining_friends[i+1:]
            # Recurse from the new state.
            candidate_schedule = search(meeting_end, friend["location"], new_remaining, new_schedule)
            # Keep the schedule with the most meetings.
            if len(candidate_schedule) > len(best_schedule):
                best_schedule = candidate_schedule
    return best_schedule

def main():
    # You arrive at Presidio at 9:00 (9*60 = 540 minutes)
    start_time = 9 * 60
    start_location = "Presidio"
    
    best_itinerary = search(start_time, start_location, friends, [])
    
    # Format the meeting times to "H:MM" strings.
    formatted_itinerary = []
    for meeting in best_itinerary:
        formatted_itinerary.append({
            "action": meeting["action"],
            "location": meeting["location"],
            "person": meeting["person"],
            "start_time": format_time(meeting["start_time"]),
            "end_time": format_time(meeting["end_time"])
        })
    
    result = {"itinerary": formatted_itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()