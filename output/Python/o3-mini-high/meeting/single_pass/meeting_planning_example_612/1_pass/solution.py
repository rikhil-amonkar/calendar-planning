#!/usr/bin/env python3
import json

# Convert time in minutes since midnight to H:MM (24-hour) string with no leading zero for hour.
def minutes_to_str(m):
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

# Travel times in minutes between locations.
# The keys are the starting locations and the inner dictionary maps destination locations to travel minutes.
travel_times = {
    "Alamo Square": {
        "Russian Hill": 13,
        "Presidio": 18,
        "Chinatown": 16,
        "Sunset District": 16,
        "The Castro": 8,
        "Embarcadero": 17,
        "Golden Gate Park": 9
    },
    "Russian Hill": {
        "Alamo Square": 15,
        "Presidio": 14,
        "Chinatown": 9,
        "Sunset District": 23,
        "The Castro": 21,
        "Embarcadero": 8,
        "Golden Gate Park": 21
    },
    "Presidio": {
        "Alamo Square": 18,
        "Russian Hill": 14,
        "Chinatown": 21,
        "Sunset District": 15,
        "The Castro": 21,
        "Embarcadero": 20,
        "Golden Gate Park": 12
    },
    "Chinatown": {
        "Alamo Square": 17,
        "Russian Hill": 7,
        "Presidio": 19,
        "Sunset District": 29,
        "The Castro": 22,
        "Embarcadero": 5,
        "Golden Gate Park": 23
    },
    "Sunset District": {
        "Alamo Square": 17,
        "Russian Hill": 24,
        "Presidio": 16,
        "Chinatown": 30,
        "The Castro": 17,
        "Embarcadero": 31,
        "Golden Gate Park": 11
    },
    "The Castro": {
        "Alamo Square": 8,
        "Russian Hill": 18,
        "Presidio": 20,
        "Chinatown": 20,
        "Sunset District": 17,
        "Embarcadero": 22,
        "Golden Gate Park": 11
    },
    "Embarcadero": {
        "Alamo Square": 19,
        "Russian Hill": 8,
        "Presidio": 20,
        "Chinatown": 7,
        "Sunset District": 31,
        "The Castro": 25,
        "Golden Gate Park": 25
    },
    "Golden Gate Park": {
        "Alamo Square": 10,
        "Russian Hill": 19,
        "Presidio": 11,
        "Chinatown": 23,
        "Sunset District": 10,
        "The Castro": 13,
        "Embarcadero": 25
    }
}

# Meeting candidate definitions.
# Times are in minutes since midnight.
# Our arrival at Alamo Square is 9:00, i.e. 540 minutes.
# Each candidate has:
#   person, location, avail_start, avail_end, and minimum meeting duration in minutes.
candidates = [
    {
        "person": "Emily",
        "location": "Russian Hill",
        "avail_start": 12 * 60 + 15,  # 12:15 => 735
        "avail_end": 14 * 60 + 15,    # 14:15 => 855
        "duration": 105
    },
    {
        "person": "Mark",
        "location": "Presidio",
        "avail_start": 14 * 60 + 45,  # 14:45 => 885
        "avail_end": 19 * 60 + 30,    # 19:30 => 1170
        "duration": 60
    },
    {
        "person": "Deborah",
        "location": "Chinatown",
        "avail_start": 7 * 60 + 30,   # 7:30 => 450
        "avail_end": 15 * 60 + 30,    # 15:30 => 930
        "duration": 45
    },
    {
        "person": "Margaret",
        "location": "Sunset District",
        "avail_start": 21 * 60 + 30,  # 21:30 => 1290
        "avail_end": 22 * 60 + 30,    # 22:30 => 1350
        "duration": 60
    },
    {
        "person": "George",
        "location": "The Castro",
        "avail_start": 7 * 60 + 30,   # 7:30 => 450
        "avail_end": 14 * 60 + 15,    # 14:15 => 855
        "duration": 60
    },
    {
        "person": "Andrew",
        "location": "Embarcadero",
        "avail_start": 20 * 60 + 15,  # 20:15 => 1215
        "avail_end": 22 * 60,         # 22:00 => 1320
        "duration": 75
    },
    {
        "person": "Steven",
        "location": "Golden Gate Park",
        "avail_start": 11 * 60 + 15,  # 11:15 => 675
        "avail_end": 21 * 60 + 15,    # 21:15 => 1275
        "duration": 105
    }
]

# We'll use DFS to try all possible orders of meetings (using each candidate at most once)
# and compute the resulting schedule if it is feasible with respect to travel times and availability windows.
# The schedule is a list of events. Each event is a dict with:
#   action, location, person, start_time (in minutes), end_time (in minutes)
def dfs(curr_loc, curr_time, remaining, schedule):
    best_schedule = schedule[:]
    # Try each candidate from the remaining list.
    for i, candidate in enumerate(remaining):
        # Get the travel time from current location to candidate's location.
        travel = travel_times[curr_loc][candidate["location"]]
        arrival = curr_time + travel
        # The meeting can only start when you both have arrived and the candidate is available.
        meeting_start = max(arrival, candidate["avail_start"])
        meeting_end = meeting_start + candidate["duration"]
        # Check if meeting can be finished before candidate's availability ends.
        if meeting_end <= candidate["avail_end"]:
            # Create the new meeting event.
            event = {
                "action": "meet",
                "location": candidate["location"],
                "person": candidate["person"],
                "start_time": meeting_start,
                "end_time": meeting_end
            }
            new_schedule = schedule + [event]
            # Exclude the candidate that was just scheduled.
            new_remaining = remaining[:i] + remaining[i+1:]
            # Recursively try to add further meetings.
            candidate_schedule = dfs(candidate["location"], meeting_end, new_remaining, new_schedule)
            # Use our selection criteria: maximize count; if equal, choose one that finishes earlier.
            if len(candidate_schedule) > len(best_schedule):
                best_schedule = candidate_schedule
            elif len(candidate_schedule) == len(best_schedule) and candidate_schedule:
                # Compare finishing times.
                if best_schedule:
                    if candidate_schedule[-1]["end_time"] < best_schedule[-1]["end_time"]:
                        best_schedule = candidate_schedule
                else:
                    best_schedule = candidate_schedule
    return best_schedule

def main():
    # Starting point: Arrive at Alamo Square at 9:00 (540 minutes)
    start_location = "Alamo Square"
    start_time = 9 * 60  # 540 minutes
    # Compute the best schedule.
    best = dfs(start_location, start_time, candidates, [])
    
    # Format the schedule itinerary with time strings.
    itinerary = []
    for event in best:
        itinerary.append({
            "action": event["action"],
            "location": event["location"],
            "person": event["person"],
            "start_time": minutes_to_str(event["start_time"]),
            "end_time": minutes_to_str(event["end_time"])
        })
    
    # Create the final dictionary.
    result = {"itinerary": itinerary}
    
    # Output the JSON result.
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()