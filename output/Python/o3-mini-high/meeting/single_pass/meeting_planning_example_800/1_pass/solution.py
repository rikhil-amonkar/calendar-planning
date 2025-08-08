#!/usr/bin/env python3
import json

def minutes_to_time(m):
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

# Travel times dictionary (in minutes)
travel_times = {
    "Union Square": {
        "The Castro": 17,
        "North Beach": 10,
        "Embarcadero": 11,
        "Alamo Square": 15,
        "Nob Hill": 9,
        "Presidio": 24,
        "Fisherman's Wharf": 15,
        "Mission District": 14,
        "Haight-Ashbury": 18
    },
    "The Castro": {
        "Union Square": 19,
        "North Beach": 20,
        "Embarcadero": 22,
        "Alamo Square": 8,
        "Nob Hill": 16,
        "Presidio": 20,
        "Fisherman's Wharf": 24,
        "Mission District": 7,
        "Haight-Ashbury": 6
    },
    "North Beach": {
        "Union Square": 7,
        "The Castro": 23,
        "Embarcadero": 6,
        "Alamo Square": 16,
        "Nob Hill": 7,
        "Presidio": 17,
        "Fisherman's Wharf": 5,
        "Mission District": 18,
        "Haight-Ashbury": 18
    },
    "Embarcadero": {
        "Union Square": 10,
        "The Castro": 25,
        "North Beach": 5,
        "Alamo Square": 19,
        "Nob Hill": 10,
        "Presidio": 20,
        "Fisherman's Wharf": 6,
        "Mission District": 20,
        "Haight-Ashbury": 21
    },
    "Alamo Square": {
        "Union Square": 14,
        "The Castro": 8,
        "North Beach": 15,
        "Embarcadero": 16,
        "Nob Hill": 11,
        "Presidio": 17,
        "Fisherman's Wharf": 19,
        "Mission District": 10,
        "Haight-Ashbury": 5
    },
    "Nob Hill": {
        "Union Square": 7,
        "The Castro": 17,
        "North Beach": 8,
        "Embarcadero": 9,
        "Alamo Square": 11,
        "Presidio": 17,
        "Fisherman's Wharf": 10,
        "Mission District": 13,
        "Haight-Ashbury": 13
    },
    "Presidio": {
        "Union Square": 22,
        "The Castro": 21,
        "North Beach": 18,
        "Embarcadero": 20,
        "Alamo Square": 19,
        "Nob Hill": 18,
        "Fisherman's Wharf": 19,
        "Mission District": 26,
        "Haight-Ashbury": 15
    },
    "Fisherman's Wharf": {
        "Union Square": 13,
        "The Castro": 27,
        "North Beach": 6,
        "Embarcadero": 8,
        "Alamo Square": 21,
        "Nob Hill": 11,
        "Presidio": 17,
        "Mission District": 22,
        "Haight-Ashbury": 22
    },
    "Mission District": {
        "Union Square": 15,
        "The Castro": 7,
        "North Beach": 17,
        "Embarcadero": 19,
        "Alamo Square": 11,
        "Nob Hill": 12,
        "Presidio": 25,
        "Fisherman's Wharf": 22,
        "Haight-Ashbury": 12
    },
    "Haight-Ashbury": {
        "Union Square": 19,
        "The Castro": 6,
        "North Beach": 19,
        "Embarcadero": 20,
        "Alamo Square": 5,
        "Nob Hill": 15,
        "Presidio": 15,
        "Fisherman's Wharf": 23,
        "Mission District": 11
    }
}

# Meetings constraints data: times in minutes since midnight.
# 9:00 AM = 540.
meetings = [
    {
        "person": "Melissa",
        "location": "The Castro",
        "avail_start": 20 * 60 + 15,  # 20:15 -> 1215
        "avail_end": 21 * 60 + 15,    # 21:15 -> 1275
        "min_duration": 30
    },
    {
        "person": "Kimberly",
        "location": "North Beach",
        "avail_start": 7 * 60 + 0,    # 7:00 -> 420
        "avail_end": 10 * 60 + 30,    # 10:30 -> 630
        "min_duration": 15
    },
    {
        "person": "Joseph",
        "location": "Embarcadero",
        "avail_start": 15 * 60 + 30,  # 15:30 -> 930
        "avail_end": 19 * 60 + 30,    # 19:30 -> 1170
        "min_duration": 75
    },
    {
        "person": "Barbara",
        "location": "Alamo Square",
        "avail_start": 20 * 60 + 45,  # 20:45 -> 1245
        "avail_end": 21 * 60 + 45,    # 21:45 -> 1305
        "min_duration": 15
    },
    {
        "person": "Kenneth",
        "location": "Nob Hill",
        "avail_start": 12 * 60 + 15,  # 12:15 -> 735
        "avail_end": 17 * 60 + 15,    # 17:15 -> 1035
        "min_duration": 105
    },
    {
        "person": "Joshua",
        "location": "Presidio",
        "avail_start": 16 * 60 + 30,  # 16:30 -> 990
        "avail_end": 18 * 60 + 15,    # 18:15 -> 1095
        "min_duration": 105
    },
    {
        "person": "Brian",
        "location": "Fisherman's Wharf",
        "avail_start": 9 * 60 + 30,   # 9:30 -> 570
        "avail_end": 15 * 60 + 30,    # 15:30 -> 930
        "min_duration": 45
    },
    {
        "person": "Steven",
        "location": "Mission District",
        "avail_start": 19 * 60 + 30,  # 19:30 -> 1170
        "avail_end": 21 * 60 + 0,     # 21:00 -> 1260
        "min_duration": 90
    },
    {
        "person": "Betty",
        "location": "Haight-Ashbury",
        "avail_start": 19 * 60 + 0,   # 19:00 -> 1140
        "avail_end": 20 * 60 + 30,    # 20:30 -> 1230
        "min_duration": 90
    }
]

# Recursive backtracking search for the optimal (maximum count) schedule.
def search(curr_time, curr_location, remaining_meetings):
    best_schedule = []
    for i, meeting in enumerate(remaining_meetings):
        # Determine travel time from current location to meeting location.
        travel_time = travel_times[curr_location][meeting["location"]]
        arrival_time = curr_time + travel_time
        # Meeting can start only when both you have arrived and the friend's availability begins.
        start_time = max(arrival_time, meeting["avail_start"])
        end_time = start_time + meeting["min_duration"]
        # Check if meeting can be completed within the friend's available time.
        if end_time <= meeting["avail_end"]:
            event = {
                "action": "meet",
                "location": meeting["location"],
                "person": meeting["person"],
                "start_time": start_time,  # stored in minutes; will convert later
                "end_time": end_time
            }
            # Remove the current meeting from the remaining list.
            next_remaining = remaining_meetings[:i] + remaining_meetings[i+1:]
            subsequent_schedule = search(end_time, meeting["location"], next_remaining)
            candidate_schedule = [event] + subsequent_schedule
            if len(candidate_schedule) > len(best_schedule):
                best_schedule = candidate_schedule
    return best_schedule

if __name__ == '__main__':
    # Start at Union Square at 9:00 AM (540 minutes)
    initial_time = 540
    initial_location = "Union Square"
    optimal_schedule = search(initial_time, initial_location, meetings)
    
    # Convert the meeting times from minutes to formatted time strings.
    for event in optimal_schedule:
        event["start_time"] = minutes_to_time(event["start_time"])
        event["end_time"] = minutes_to_time(event["end_time"])
    
    result = {"itinerary": optimal_schedule}
    print(json.dumps(result))