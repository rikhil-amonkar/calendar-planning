#!/usr/bin/env python3
import json
import itertools

# Helper function to convert minutes (from midnight) into H:MM format (24-hour, no leading zero for hour)
def minute_to_time_str(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

# Travel times in minutes between locations (directional)
travel_times = {
    "Haight-Ashbury": {
        "Fisherman's Wharf": 23,
        "Richmond District": 10,
        "Mission District": 11,
        "Bayview": 18
    },
    "Fisherman's Wharf": {
        "Haight-Ashbury": 22,
        "Richmond District": 18,
        "Mission District": 22,
        "Bayview": 26
    },
    "Richmond District": {
        "Haight-Ashbury": 10,
        "Fisherman's Wharf": 18,
        "Mission District": 20,
        "Bayview": 26
    },
    "Mission District": {
        "Haight-Ashbury": 12,
        "Fisherman's Wharf": 22,
        "Richmond District": 20,
        "Bayview": 15
    },
    "Bayview": {
        "Haight-Ashbury": 19,
        "Fisherman's Wharf": 25,
        "Richmond District": 25,
        "Mission District": 13
    }
}

# Define meeting constraints for each friend
# Times are represented in minutes from midnight.
# 9:00AM is 540 minutes; Also:
#   13:00 -> 780, 14:45 -> 885, 15:15 -> 915,
#   17:30 -> 1050, 18:45 -> 1125, 19:15 -> 1155,
#   21:45 -> 1305, 22:30 -> 1350.
meetings = [
    {
        "person": "Sarah",
        "location": "Fisherman's Wharf",
        "avail_start": 885,   # 14:45
        "avail_end":   1050,  # 17:30
        "duration":    105    # minutes
    },
    {
        "person": "Mary",
        "location": "Richmond District",
        "avail_start": 780,   # 13:00
        "avail_end":   1155,  # 19:15
        "duration":    75
    },
    {
        "person": "Helen",
        "location": "Mission District",
        "avail_start": 1305,  # 21:45
        "avail_end":   1350,  # 22:30
        "duration":    30
    },
    {
        "person": "Thomas",
        "location": "Bayview",
        "avail_start": 915,   # 15:15
        "avail_end":   1125,  # 18:45
        "duration":    120
    }
]

# Function to try scheduling a given ordered sequence of meetings.
# Returns a list of scheduled meeting events (with computed start and end times in minutes)
# if the order is feasible or None if any meeting cannot be scheduled within its window.
def try_schedule(order):
    schedule = []
    current_time = 540  # Starting at 9:00 AM (540 minutes)
    current_location = "Haight-Ashbury"
    for meeting in order:
        # Get travel time from current location to meeting location.
        if current_location not in travel_times or meeting["location"] not in travel_times[current_location]:
            return None
        travel = travel_times[current_location][meeting["location"]]
        arrival_time = current_time + travel
        # Meeting cannot start before the friend is available.
        meeting_start = max(arrival_time, meeting["avail_start"])
        meeting_end = meeting_start + meeting["duration"]
        # Check if the meeting can finish before the friend leaves.
        if meeting_end > meeting["avail_end"]:
            return None
        # Record the scheduled meeting (times are in minutes until later conversion)
        schedule.append({
            "person": meeting["person"],
            "location": meeting["location"],
            "start_time": meeting_start,
            "end_time": meeting_end
        })
        current_time = meeting_end
        current_location = meeting["location"]
    return schedule

def main():
    best_schedule = None
    best_count = 0
    best_finish_time = float('inf')
    
    # We want to maximize the number of friends met.
    # Try all possible orders from subsets of the meetings.
    for r in range(1, len(meetings) + 1):
        for order in itertools.permutations(meetings, r):
            sched = try_schedule(order)
            if sched is not None:
                count = len(sched)
                finish_time = sched[-1]["end_time"]
                # Prefer a schedule with more meetings.
                # If the number of meetings ties, choose the one that finishes earlier.
                if count > best_count or (count == best_count and finish_time < best_finish_time):
                    best_schedule = sched
                    best_count = count
                    best_finish_time = finish_time

    # Only output the scheduled meeting events as required.
    itinerary = []
    if best_schedule is not None:
        for event in best_schedule:
            itinerary.append({
                "action": "meet",
                "location": event["location"],
                "person": event["person"],
                "start_time": minute_to_time_str(event["start_time"]),
                "end_time": minute_to_time_str(event["end_time"])
            })
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()