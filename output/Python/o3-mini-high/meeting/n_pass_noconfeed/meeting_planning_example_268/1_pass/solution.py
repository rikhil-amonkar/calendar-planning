import itertools
import json

def time_to_minutes(time_str):
    # time_str format: "H:MM" (24-hour format)
    parts = time_str.split(":")
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

# Define travel times (in minutes) between locations
travel_times = {
    "Golden Gate Park": {"Alamo Square": 10, "Presidio": 11, "Russian Hill": 19},
    "Alamo Square": {"Golden Gate Park": 9, "Presidio": 18, "Russian Hill": 13},
    "Presidio": {"Golden Gate Park": 12, "Alamo Square": 18, "Russian Hill": 14},
    "Russian Hill": {"Golden Gate Park": 21, "Alamo Square": 15, "Presidio": 14}
}

# Define friends with their meeting details:
# Each friend is available at a fixed location with a time window and a minimum meeting duration.
friends = {
    "Timothy": {
        "location": "Alamo Square",
        "avail_start": time_to_minutes("12:00"),
        "avail_end": time_to_minutes("16:15"),
        "duration": 105
    },
    "Mark": {
        "location": "Presidio",
        "avail_start": time_to_minutes("18:45"),
        "avail_end": time_to_minutes("21:00"),
        "duration": 60
    },
    "Joseph": {
        "location": "Russian Hill",
        "avail_start": time_to_minutes("16:45"),
        "avail_end": time_to_minutes("21:30"),
        "duration": 60
    }
}

def compute_schedule(order):
    itinerary = []
    # Start at Golden Gate Park at 9:00AM
    current_time = time_to_minutes("9:00")
    current_location = "Golden Gate Park"
    
    for friend in order:
        friend_details = friends[friend]
        # Travel from current location to friend's meeting location
        travel_time = travel_times[current_location][friend_details["location"]]
        arrival_time = current_time + travel_time
        # Meeting can only start when friend is available
        meeting_start = max(arrival_time, friend_details["avail_start"])
        meeting_end = meeting_start + friend_details["duration"]
        # Check if meeting ends before friend's available end time
        if meeting_end > friend_details["avail_end"]:
            return None, None  # Not feasible
        # Append meeting details to itinerary
        itinerary.append({
            "action": "meet",
            "location": friend_details["location"],
            "person": friend,
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        })
        # Update current time and location after meeting
        current_time = meeting_end
        current_location = friend_details["location"]
    return itinerary, current_time

def main():
    friend_names = list(friends.keys())
    best_itinerary = None
    best_finish_time = None

    # Try all permutations of friend meeting orders
    for order in itertools.permutations(friend_names):
        itinerary, finish_time = compute_schedule(order)
        if itinerary is None:
            continue  # skip infeasible orders
        if best_finish_time is None or finish_time < best_finish_time:
            best_finish_time = finish_time
            best_itinerary = itinerary

    # If a best itinerary is found, output in the required JSON format
    output = {"itinerary": best_itinerary if best_itinerary is not None else []}
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()