#!/usr/bin/env python3
import json

# Helper function to convert minutes after midnight to H:MM (24-hour format, no leading zero for hour)
def minutes_to_time_str(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Predefined travel times (in minutes) between locations.
# The keys are location names and each value is a dictionary mapping destination location to travel time.
travel_times = {
    "Nob Hill": {
        "Embarcadero": 9,
        "The Castro": 17,
        "Haight-Ashbury": 13,
        "Union Square": 7,
        "North Beach": 8,
        "Pacific Heights": 8,
        "Chinatown": 6,
        "Golden Gate Park": 17,
        "Marina District": 11,
        "Russian Hill": 5
    },
    "Embarcadero": {
        "Nob Hill": 10,
        "The Castro": 25,
        "Haight-Ashbury": 21,
        "Union Square": 10,
        "North Beach": 5,
        "Pacific Heights": 11,
        "Chinatown": 7,
        "Golden Gate Park": 25,
        "Marina District": 12,
        "Russian Hill": 8
    },
    "The Castro": {
        "Nob Hill": 16,
        "Embarcadero": 22,
        "Haight-Ashbury": 6,
        "Union Square": 19,
        "North Beach": 20,
        "Pacific Heights": 16,
        "Chinatown": 22,
        "Golden Gate Park": 11,
        "Marina District": 21,
        "Russian Hill": 18
    },
    "Haight-Ashbury": {
        "Nob Hill": 15,
        "Embarcadero": 20,
        "The Castro": 6,
        "Union Square": 19,
        "North Beach": 19,
        "Pacific Heights": 12,
        "Chinatown": 19,
        "Golden Gate Park": 7,
        "Marina District": 17,
        "Russian Hill": 17
    },
    "Union Square": {
        "Nob Hill": 9,
        "Embarcadero": 11,
        "The Castro": 17,
        "Haight-Ashbury": 18,
        "North Beach": 10,
        "Pacific Heights": 15,
        "Chinatown": 7,
        "Golden Gate Park": 22,
        "Marina District": 18,
        "Russian Hill": 13
    },
    "North Beach": {
        "Nob Hill": 7,
        "Embarcadero": 6,
        "The Castro": 23,
        "Haight-Ashbury": 18,
        "Union Square": 7,
        "Pacific Heights": 8,
        "Chinatown": 6,
        "Golden Gate Park": 22,
        "Marina District": 9,
        "Russian Hill": 4
    },
    "Pacific Heights": {
        "Nob Hill": 8,
        "Embarcadero": 10,
        "The Castro": 16,
        "Haight-Ashbury": 11,
        "Union Square": 12,
        "North Beach": 9,
        "Chinatown": 11,
        "Golden Gate Park": 15,
        "Marina District": 6,
        "Russian Hill": 7
    },
    "Chinatown": {
        "Nob Hill": 9,
        "Embarcadero": 5,
        "The Castro": 22,
        "Haight-Ashbury": 19,
        "Union Square": 7,
        "North Beach": 3,
        "Pacific Heights": 10,
        "Golden Gate Park": 23,
        "Marina District": 12,
        "Russian Hill": 7
    },
    "Golden Gate Park": {
        "Nob Hill": 20,
        "Embarcadero": 25,
        "The Castro": 13,
        "Haight-Ashbury": 7,
        "Union Square": 22,
        "North Beach": 23,
        "Pacific Heights": 16,
        "Chinatown": 23,
        "Marina District": 16,
        "Russian Hill": 19
    },
    "Marina District": {
        "Nob Hill": 12,
        "Embarcadero": 14,
        "The Castro": 22,
        "Haight-Ashbury": 16,
        "Union Square": 16,
        "North Beach": 11,
        "Pacific Heights": 7,
        "Chinatown": 15,
        "Golden Gate Park": 18,
        "Russian Hill": 8
    },
    "Russian Hill": {
        "Nob Hill": 5,
        "Embarcadero": 8,
        "The Castro": 21,
        "Haight-Ashbury": 17,
        "Union Square": 10,
        "North Beach": 5,
        "Pacific Heights": 7,
        "Chinatown": 9,
        "Golden Gate Park": 21,
        "Marina District": 7
    }
}

# Meeting constraints.
# Each meeting is defined with: person, location, available start and end time (in minutes after midnight), and required duration (in minutes)
# Times are converted as follows:
# 9:00AM = 540, 11:15AM = 675, 11:45AM = 705, 13:15 = 795, 13:45 = 825, 17:30 = 1050, 19:15 = 1155, 19:45 = 1185, 20:00 = 1200, etc.
meetings = [
    {
        "id": "Mary",
        "person": "Mary",
        "location": "Embarcadero",
        "avail_start": 20 * 60,         # 20:00 -> 1200
        "avail_end": 21 * 60 + 15,        # 21:15 -> 1275
        "duration": 75
    },
    {
        "id": "Kenneth",
        "person": "Kenneth",
        "location": "The Castro",
        "avail_start": 11 * 60 + 15,      # 11:15 -> 675
        "avail_end": 19 * 60 + 15,        # 19:15 -> 1155
        "duration": 30
    },
    {
        "id": "Joseph",
        "person": "Joseph",
        "location": "Haight-Ashbury",
        "avail_start": 20 * 60,           # 20:00 -> 1200
        "avail_end": 22 * 60,             # 22:00 -> 1320
        "duration": 120
    },
    {
        "id": "Sarah",
        "person": "Sarah",
        "location": "Union Square",
        "avail_start": 11 * 60 + 45,      # 11:45 -> 705
        "avail_end": 14 * 60 + 30,        # 14:30 -> 870
        "duration": 90
    },
    {
        "id": "Thomas",
        "person": "Thomas",
        "location": "North Beach",
        "avail_start": 19 * 60 + 15,      # 19:15 -> 1155
        "avail_end": 19 * 60 + 45,        # 19:45 -> 1185
        "duration": 15
    },
    {
        "id": "Daniel",
        "person": "Daniel",
        "location": "Pacific Heights",
        "avail_start": 13 * 60 + 45,      # 13:45 -> 825
        "avail_end": 20 * 60 + 30,        # 20:30 -> 1230
        "duration": 15
    },
    {
        "id": "Richard",
        "person": "Richard",
        "location": "Chinatown",
        "avail_start": 8 * 60,            # 8:00 -> 480
        "avail_end": 18 * 60 + 45,        # 18:45 -> 1125
        "duration": 30
    },
    {
        "id": "Mark",
        "person": "Mark",
        "location": "Golden Gate Park",
        "avail_start": 17 * 60 + 30,      # 17:30 -> 1050
        "avail_end": 21 * 60 + 30,        # 21:30 -> 1290
        "duration": 120
    },
    {
        "id": "David",
        "person": "David",
        "location": "Marina District",
        "avail_start": 20 * 60,           # 20:00 -> 1200
        "avail_end": 21 * 60,             # 21:00 -> 1260
        "duration": 60
    },
    {
        "id": "Karen",
        "person": "Karen",
        "location": "Russian Hill",
        "avail_start": 13 * 60 + 15,      # 13:15 -> 795
        "avail_end": 18 * 60 + 30,        # 18:30 -> 1110
        "duration": 120
    }
]

# For efficient lookup later, create a dictionary mapping meeting id to meeting details.
meetings_by_id = {m["id"]: m for m in meetings}
all_ids = set(m["id"] for m in meetings)

# Use DFS with memoization to search for the schedule that maximizes the number of meetings.
# State is (current_location, current_time, frozenset(remaining_meeting_ids)).
memo = {}

def dfs(curr_loc, curr_time, remaining):
    state = (curr_loc, curr_time, frozenset(remaining))
    if state in memo:
        return memo[state]
        
    best_count = 0
    best_plan = []  # list of scheduled meeting events
    
    # Try each meeting in the remaining set
    for mid in list(remaining):
        meeting = meetings_by_id[mid]
        # Get travel time from current location to candidate meeting location.
        travel = travel_times[curr_loc][meeting["location"]]
        arrival_time = curr_time + travel
        # Meeting can start at the later of arrival time and the meeting's available start.
        scheduled_start = max(arrival_time, meeting["avail_start"])
        scheduled_end = scheduled_start + meeting["duration"]
        # Check if we can complete the meeting within the available window.
        if scheduled_end <= meeting["avail_end"]:
            # This meeting is feasible.
            new_remaining = set(remaining)
            new_remaining.remove(mid)
            # Recursively compute schedule from the end of this meeting.
            count_next, plan_next = dfs(meeting["location"], scheduled_end, new_remaining)
            count_total = 1 + count_next
            if count_total > best_count:
                # Create a meeting event dictionary.
                event = {
                    "action": "meet",
                    "location": meeting["location"],
                    "person": meeting["person"],
                    "start_time": scheduled_start,  # will convert later
                    "end_time": scheduled_end      # will convert later
                }
                best_plan = [event] + plan_next
                best_count = count_total
    memo[state] = (best_count, best_plan)
    return memo[state]

def main():
    # Starting point: Arrive at Nob Hill at 9:00 AM (540 minutes after midnight)
    start_location = "Nob Hill"
    start_time = 9 * 60  # 9:00 -> 540
    max_count, best_itinerary = dfs(start_location, start_time, all_ids)
    
    # Convert meeting start and end times (in minutes) to H:MM strings.
    for event in best_itinerary:
        event["start_time"] = minutes_to_time_str(event["start_time"])
        event["end_time"] = minutes_to_time_str(event["end_time"])
    
    # Build resulting dictionary in the required JSON structure.
    result = {
        "itinerary": best_itinerary
    }
    
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()