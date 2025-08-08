#!/usr/bin/env python3
import json

# Helper function: convert minutes-since-midnight to "H:MM" string (24-hour format)
def minutes_to_timestr(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

# Travel times dictionary (in minutes)
travel_times = {
    "Presidio": {
        "Haight-Ashbury": 15,
        "Nob Hill": 18,
        "Russian Hill": 14,
        "North Beach": 18,
        "Chinatown": 21,
        "Union Square": 22,
        "Embarcadero": 20,
        "Financial District": 23,
        "Marina District": 11
    },
    "Haight-Ashbury": {
        "Presidio": 15,
        "Nob Hill": 15,
        "Russian Hill": 17,
        "North Beach": 19,
        "Chinatown": 19,
        "Union Square": 19,
        "Embarcadero": 20,
        "Financial District": 21,
        "Marina District": 17
    },
    "Nob Hill": {
        "Presidio": 17,
        "Haight-Ashbury": 13,
        "Russian Hill": 5,
        "North Beach": 8,
        "Chinatown": 6,
        "Union Square": 7,
        "Embarcadero": 9,
        "Financial District": 9,
        "Marina District": 11
    },
    "Russian Hill": {
        "Presidio": 14,
        "Haight-Ashbury": 17,
        "Nob Hill": 5,
        "North Beach": 5,
        "Chinatown": 9,
        "Union Square": 10,
        "Embarcadero": 8,
        "Financial District": 11,
        "Marina District": 7
    },
    "North Beach": {
        "Presidio": 17,
        "Haight-Ashbury": 18,
        "Nob Hill": 7,
        "Russian Hill": 4,
        "Chinatown": 6,
        "Union Square": 10,
        "Embarcadero": 6,
        "Financial District": 8,
        "Marina District": 9
    },
    "Chinatown": {
        "Presidio": 19,
        "Haight-Ashbury": 19,
        "Nob Hill": 9,
        "Russian Hill": 7,
        "North Beach": 3,
        "Union Square": 7,
        "Embarcadero": 5,
        "Financial District": 5,
        "Marina District": 12
    },
    "Union Square": {
        "Presidio": 24,
        "Haight-Ashbury": 18,
        "Nob Hill": 9,
        "Russian Hill": 13,
        "North Beach": 10,
        "Chinatown": 7,
        "Embarcadero": 11,
        "Financial District": 9,
        "Marina District": 18
    },
    "Embarcadero": {
        "Presidio": 20,
        "Haight-Ashbury": 21,
        "Nob Hill": 10,
        "Russian Hill": 8,
        "North Beach": 5,
        "Chinatown": 7,
        "Union Square": 10,
        "Financial District": 5,
        "Marina District": 12
    },
    "Financial District": {
        "Presidio": 22,
        "Haight-Ashbury": 19,
        "Nob Hill": 8,
        "Russian Hill": 11,
        "North Beach": 7,
        "Chinatown": 5,
        "Union Square": 9,
        "Embarcadero": 4,
        "Marina District": 15
    },
    "Marina District": {
        "Presidio": 10,
        "Haight-Ashbury": 16,
        "Nob Hill": 12,
        "Russian Hill": 8,
        "North Beach": 11,
        "Chinatown": 15,
        "Union Square": 16,
        "Embarcadero": 14,
        "Financial District": 17
    }
}

# Meeting constraints for each friend.
# All times are converted into minutes from midnight.
# Format: {"name": <name>, "location": <location>, "avail_start": <start in minutes>, "avail_end": <end in minutes>, "duration": <required meeting duration in minutes>}
meetings = [
    {
        "name": "Karen",
        "location": "Haight-Ashbury",
        "avail_start": 21 * 60,          # 21:00 -> 1260
        "avail_end": 21 * 60 + 45,         # 21:45 -> 1305
        "duration": 45
    },
    {
        "name": "Jessica",
        "location": "Nob Hill",
        "avail_start": 13 * 60 + 45,       # 13:45 -> 825
        "avail_end": 21 * 60,              # 21:00 -> 1260
        "duration": 90
    },
    {
        "name": "Brian",
        "location": "Russian Hill",
        "avail_start": 15 * 60 + 30,       # 15:30 -> 930
        "avail_end": 21 * 60 + 45,         # 21:45 -> 1305
        "duration": 60
    },
    {
        "name": "Kenneth",
        "location": "North Beach",
        "avail_start": 9 * 60 + 45,        # 9:45 -> 585
        "avail_end": 21 * 60,              # 21:00 -> 1260
        "duration": 30
    },
    {
        "name": "Jason",
        "location": "Chinatown",
        "avail_start": 8 * 60 + 15,        # 8:15 -> 495
        "avail_end": 11 * 60 + 45,         # 11:45 -> 705
        "duration": 75
    },
    {
        "name": "Stephanie",
        "location": "Union Square",
        "avail_start": 14 * 60 + 45,       # 14:45 -> 885
        "avail_end": 18 * 60 + 45,         # 18:45 -> 1125
        "duration": 105
    },
    {
        "name": "Kimberly",
        "location": "Embarcadero",
        "avail_start": 9 * 60 + 45,        # 9:45 -> 585
        "avail_end": 19 * 60 + 30,         # 19:30 -> 1170
        "duration": 75
    },
    {
        "name": "Steven",
        "location": "Financial District",
        "avail_start": 7 * 60 + 15,        # 7:15 -> 435
        "avail_end": 21 * 60 + 15,         # 21:15 -> 1275
        "duration": 60
    },
    {
        "name": "Mark",
        "location": "Marina District",
        "avail_start": 10 * 60 + 15,       # 10:15 -> 615
        "avail_end": 13 * 60,              # 13:00 -> 780
        "duration": 75
    }
]

# Recursive DFS function to search for the optimal schedule that maximizes the number of meetings.
def dfs(current_time, current_loc, remaining):
    best_schedule = []
    # Try each meeting in the remaining list
    for i, meeting in enumerate(remaining):
        # Calculate travel time from current location to the meeting's location
        travel = travel_times[current_loc][meeting["location"]]
        arrival_time = current_time + travel
        # The meeting can only start when the person is available.
        meeting_start = max(arrival_time, meeting["avail_start"])
        meeting_end = meeting_start + meeting["duration"]
        # Check if the meeting can be completed within the friend's available window.
        if meeting_end <= meeting["avail_end"]:
            # Create an event dictionary for this meeting.
            event = {
                "action": "meet",
                "location": meeting["location"],
                "person": meeting["name"],
                "start_time": minutes_to_timestr(meeting_start),
                "end_time": minutes_to_timestr(meeting_end)
            }
            # Remove the meeting from the remaining list for the next recursion.
            next_remaining = remaining[:i] + remaining[i+1:]
            # Recursively search for subsequent meetings.
            subsequent_schedule = dfs(meeting_end, meeting["location"], next_remaining)
            candidate_schedule = [event] + subsequent_schedule
            # Choose the candidate with the most meetings.
            if len(candidate_schedule) > len(best_schedule):
                best_schedule = candidate_schedule
    return best_schedule

if __name__ == '__main__':
    # Starting conditions: Arrive at Presidio at 9:00 (9*60 = 540 minutes)
    start_time = 9 * 60
    start_location = "Presidio"
    optimal_itinerary = dfs(start_time, start_location, meetings)
    
    # Create the result dictionary and output as JSON.
    result = {
        "itinerary": optimal_itinerary
    }
    print(json.dumps(result))