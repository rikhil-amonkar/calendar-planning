#!/usr/bin/env python3
import json
import sys

# Convert time in minutes (since midnight) to string in "H:MM" 24-hour format (no leading zero for hour)
def minutes_to_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

# Travel times dictionary (in minutes) as given in the problem statement
travel_times = {
    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "Embarcadero"): 8,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Russian Hill", "Mission District"): 16,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Bayview"): 23,
    ("Russian Hill", "Richmond District"): 14,
    
    ("Pacific Heights", "Russian Hill"): 7,
    ("Pacific Heights", "North Beach"): 9,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Embarcadero"): 10,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Bayview"): 22,
    ("Pacific Heights", "Richmond District"): 12,
    
    ("North Beach", "Russian Hill"): 4,
    ("North Beach", "Pacific Heights"): 8,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "Haight-Ashbury"): 18,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Mission District"): 18,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Bayview"): 25,
    ("North Beach", "Richmond District"): 18,
    
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "North Beach"): 23,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "Alamo Square"): 9,
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "Richmond District"): 7,
    
    ("Embarcadero", "Russian Hill"): 8,
    ("Embarcadero", "Pacific Heights"): 11,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Haight-Ashbury"): 21,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Mission District"): 20,
    ("Embarcadero", "Alamo Square"): 19,
    ("Embarcadero", "Bayview"): 21,
    ("Embarcadero", "Richmond District"): 21,
    
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "North Beach"): 19,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Embarcadero"): 20,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "Richmond District"): 10,
    
    ("Fisherman's Wharf", "Russian Hill"): 7,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Alamo Square"): 21,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Richmond District"): 18,
    
    ("Mission District", "Russian Hill"): 15,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "North Beach"): 17,
    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "Embarcadero"): 19,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "Bayview"): 14,
    ("Mission District", "Richmond District"): 20,
    
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Pacific Heights"): 10,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Embarcadero"): 16,
    ("Alamo Square", "Haight-Ashbury"): 5,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Alamo Square", "Mission District"): 10,
    ("Alamo Square", "Bayview"): 16,
    ("Alamo Square", "Richmond District"): 11,
    
    ("Bayview", "Russian Hill"): 23,
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "North Beach"): 22,
    ("Bayview", "Golden Gate Park"): 22,
    ("Bayview", "Embarcadero"): 19,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Mission District"): 13,
    ("Bayview", "Alamo Square"): 16,
    ("Bayview", "Richmond District"): 25,
    
    ("Richmond District", "Russian Hill"): 13,
    ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "North Beach"): 17,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Mission District"): 20,
    ("Richmond District", "Alamo Square"): 13,
    ("Richmond District", "Bayview"): 27,
}

# List of meetings (each meeting is a friend with their constraints)
# Times are converted to minutes since midnight.
# Availability windows:
# Emily: Pacific Heights 9:15 (555) to 13:45 (825), min 120 mins
# Helen: North Beach 13:45 (825) to 18:45 (1125), min 30 mins
# Kimberly: Golden Gate Park 18:45 (1125) to 21:15 (1275), min 75 mins
# James: Embarcadero 10:30 (630) to 11:30 (690), min 30 mins
# Linda: Haight-Ashbury 7:30 (450) to 19:15 (1155), min 15 mins
# Paul: Fisherman's Wharf 14:45 (885) to 18:45 (1125), min 90 mins
# Anthony: Mission District 8:00 (480) to 14:45 (885), min 105 mins
# Nancy: Alamo Square 8:30 (510) to 13:45 (825), min 120 mins
# William: Bayview 17:30 (1050) to 20:30 (1230), min 120 mins
# Margaret: Richmond District 15:15 (915) to 18:15 (1095), min 45 mins
meetings = [
    {"person": "Emily", "location": "Pacific Heights", "avail_start": 555, "avail_end": 825, "duration": 120},
    {"person": "Helen", "location": "North Beach", "avail_start": 825, "avail_end": 1125, "duration": 30},
    {"person": "Kimberly", "location": "Golden Gate Park", "avail_start": 1125, "avail_end": 1275, "duration": 75},
    {"person": "James", "location": "Embarcadero", "avail_start": 630, "avail_end": 690, "duration": 30},
    {"person": "Linda", "location": "Haight-Ashbury", "avail_start": 450, "avail_end": 1155, "duration": 15},
    {"person": "Paul", "location": "Fisherman's Wharf", "avail_start": 885, "avail_end": 1125, "duration": 90},
    {"person": "Anthony", "location": "Mission District", "avail_start": 480, "avail_end": 885, "duration": 105},
    {"person": "Nancy", "location": "Alamo Square", "avail_start": 510, "avail_end": 825, "duration": 120},
    {"person": "William", "location": "Bayview", "avail_start": 1050, "avail_end": 1230, "duration": 120},
    {"person": "Margaret", "location": "Richmond District", "avail_start": 915, "avail_end": 1095, "duration": 45},
]

# Global best schedule variables
best_schedule = []
best_count = 0

# Recursive DFS search for the maximum number of meetings that can be scheduled.
def search(current_location, current_time, scheduled, remaining):
    global best_schedule, best_count
    # Update best_schedule if current scheduled count is higher than best_count so far.
    if len(scheduled) > best_count:
        best_count = len(scheduled)
        best_schedule = scheduled[:]
    # Try to schedule each remaining meeting one by one.
    for i, meeting in enumerate(remaining):
        # Lookup travel time from current_location to meeting location.
        key = (current_location, meeting["location"])
        if key not in travel_times:
            continue
        travel = travel_times[key]
        arrival = current_time + travel
        # The meeting can only start after the participant's available start time.
        start_meet = max(arrival, meeting["avail_start"])
        end_meet = start_meet + meeting["duration"]
        # Check if meeting can finish within the participant's availability window.
        if end_meet <= meeting["avail_end"]:
            # Create a new itinerary entry for this meeting.
            scheduled_item = {
                "action": "meet",
                "location": meeting["location"],
                "person": meeting["person"],
                "start_time": minutes_to_time(start_meet),
                "end_time": minutes_to_time(end_meet)
            }
            # New state after scheduling this meeting.
            new_scheduled = scheduled + [scheduled_item]
            # Exclude the current meeting and continue the search.
            new_remaining = remaining[:i] + remaining[i+1:]
            search(meeting["location"], end_meet, new_scheduled, new_remaining)

def main():
    # Starting state: at Russian Hill at 9:00 AM (540 minutes)
    start_location = "Russian Hill"
    start_time = 540  # 9:00 AM in minutes
    search(start_location, start_time, [], meetings)
    # Prepare the final itinerary as a JSON dictionary.
    result = {"itinerary": best_schedule}
    # Output the result as a JSON-formatted dictionary.
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()