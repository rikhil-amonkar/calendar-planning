import json
import itertools

# Helper function to convert minutes since midnight to "H:MM" string (24-hour format)
def minutes_to_str(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

# Travel times in minutes between locations
travel_times = {
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "Mission District"): 13,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Financial District"): 19,
    ("Pacific Heights", "Bayview"): 22,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Financial District"): 13,
    ("Mission District", "Bayview"): 15,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Financial District"): 17,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Financial District", "Bayview"): 19,
    ("Financial District", "Pacific Heights"): 13,
    ("Financial District", "Mission District"): 17,
    ("Financial District", "Haight-Ashbury"): 19
}

# Meeting constraints for each friend.
# Times are in minutes since midnight.
# Bayview arrival: 9:00 AM = 540
# Mary: location Pacific Heights, available 10:00 (600) to 19:00 (1140), duration 45.
# Lisa: location Mission District, available 20:30 (1230) to 22:00 (1320), duration 75.
# Betty: location Haight-Ashbury, available 7:15 (435) to 17:15 (1035), duration 90.
# Charles: location Financial District, available 11:15 (675) to 15:00 (900), duration 120.
friends = [
    {
        "name": "Mary",
        "location": "Pacific Heights",
        "avail_start": 600,
        "avail_end": 1140,
        "duration": 45
    },
    {
        "name": "Lisa",
        "location": "Mission District",
        "avail_start": 1230,
        "avail_end": 1320,
        "duration": 75
    },
    {
        "name": "Betty",
        "location": "Haight-Ashbury",
        "avail_start": 435,
        "avail_end": 1035,
        "duration": 90
    },
    {
        "name": "Charles",
        "location": "Financial District",
        "avail_start": 675,
        "avail_end": 900,
        "duration": 120
    }
]

# Compute the schedule for a given order of meetings.
# Returns a tuple: (total_waiting_time, finish_time, itinerary)
def compute_schedule(order):
    itinerary = []
    total_wait = 0
    # You start at Bayview at 9:00 AM (540 minutes)
    current_time = 540
    current_location = "Bayview"
    
    for friend in order:
        # Calculate travel time from current location to friend's location
        travel_key = (current_location, friend["location"])
        travel_time = travel_times.get(travel_key, None)
        if travel_time is None:
            # if no route, schedule is not feasible
            return None
        arrival = current_time + travel_time
        # Meeting can start only when the friend is available
        meeting_start = max(arrival, friend["avail_start"])
        wait_time = meeting_start - arrival
        total_wait += wait_time
        meeting_end = meeting_start + friend["duration"]
        # Check if meeting fits in the friend's available window
        if meeting_end > friend["avail_end"]:
            return None
        # Append the meeting event to the itinerary
        itinerary.append({
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": minutes_to_str(meeting_start),
            "end_time": minutes_to_str(meeting_end)
        })
        # Update current time and location for the next meeting
        current_time = meeting_end
        current_location = friend["location"]
    
    return total_wait, current_time, itinerary

def main():
    # Since Lisa is only available in the evening, she must be scheduled last.
    others = [f for f in friends if f["name"] != "Lisa"]
    lisa_friend = [f for f in friends if f["name"] == "Lisa"][0]
    
    valid_schedules = []
    # Generate all possible orders for the other meetings and then add Lisa at the end.
    for perm in itertools.permutations(others):
        order = list(perm) + [lisa_friend]
        result = compute_schedule(order)
        if result is not None:
            total_wait, finish_time, itinerary = result
            valid_schedules.append((total_wait, finish_time, itinerary))
    
    # Choose the schedule with minimal total waiting time, and if tied, then the one finishing earliest.
    if not valid_schedules:
        optimal_itinerary = []
    else:
        best = min(valid_schedules, key=lambda x: (x[0], x[1]))
        optimal_itinerary = best[2]
    
    # Prepare the output dictionary according to the required JSON structure.
    output = {"itinerary": optimal_itinerary}
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()