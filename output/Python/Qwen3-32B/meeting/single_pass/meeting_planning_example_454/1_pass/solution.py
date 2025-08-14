import itertools
import json

# Define friends with their details
friends = [
    {
        "name": "Daniel",
        "location": "Mission District",
        "available_start": 7 * 60 + 0,  # 7:00 AM
        "available_end": 11 * 60 + 15,  # 11:15 AM
        "meeting_duration": 105
    },
    {
        "name": "Ronald",
        "location": "Chinatown",
        "available_start": 7 * 60 + 15,  # 7:15 AM
        "available_end": 14 * 60 + 45,  # 2:45 PM
        "meeting_duration": 90
    },
    {
        "name": "William",
        "location": "North Beach",
        "available_start": 13 * 60 + 15,  # 1:15 PM
        "available_end": 20 * 60 + 15,  # 8:15 PM
        "meeting_duration": 15
    },
    {
        "name": "Jessica",
        "location": "Golden Gate Park",
        "available_start": 13 * 60 + 45,  # 1:45 PM
        "available_end": 15 * 60 + 0,  # 3:00 PM
        "meeting_duration": 30
    },
    {
        "name": "Ashley",
        "location": "Bayview",
        "available_start": 17 * 60 + 15,  # 5:15 PM
        "available_end": 20 * 60 + 0,  # 8:00 PM
        "meeting_duration": 105
    }
]

# Define travel times between locations
travel_time = {
    "Presidio": {
        "Golden Gate Park": 12,
        "Bayview": 31,
        "Chinatown": 21,
        "North Beach": 18,
        "Mission District": 26
    },
    "Golden Gate Park": {
        "Presidio": 11,
        "Bayview": 23,
        "Chinatown": 23,
        "North Beach": 24,
        "Mission District": 17
    },
    "Bayview": {
        "Presidio": 31,
        "Golden Gate Park": 22,
        "Chinatown": 18,
        "North Beach": 21,
        "Mission District": 13
    },
    "Chinatown": {
        "Presidio": 19,
        "Golden Gate Park": 23,
        "Bayview": 22,
        "North Beach": 3,
        "Mission District": 18
    },
    "North Beach": {
        "Presidio": 17,
        "Golden Gate Park": 22,
        "Bayview": 22,
        "Chinatown": 6,
        "Mission District": 18
    },
    "Mission District": {
        "Presidio": 25,
        "Golden Gate Park": 17,
        "Bayview": 15,
        "Chinatown": 16,
        "North Beach": 17
    }
}

def minutes_to_time_str(minutes):
    """Convert minutes since midnight to 'H:MM' string in 24-hour format."""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def is_valid_schedule(friends_order):
    """Check if the given order of friends can be visited in sequence."""
    current_time = 9 * 60  # 9:00 AM in minutes
    current_location = "Presidio"
    meetings = []

    for friend in friends_order:
        # Get travel time from current location to friend's location
        dest = friend["location"]
        travel = travel_time[current_location][dest]
        arrival_time = current_time + travel

        # Check if arrival time is before friend's end time and meeting can fit
        friend_start = friend["available_start"]
        friend_end = friend["available_end"]
        duration = friend["meeting_duration"]

        # Meeting can start at max(arrival_time, friend_start)
        start_time = max(arrival_time, friend_start)
        end_time = start_time + duration

        if end_time > friend_end:
            return None  # Invalid schedule

        # Record the meeting
        meetings.append({
            "action": "meet",
            "location": dest,
            "person": friend["name"],
            "start_time": minutes_to_time_str(start_time),
            "end_time": minutes_to_time_str(end_time)
        })

        # Update current time and location
        current_time = end_time
        current_location = dest

    return meetings  # Valid schedule

def find_optimal_schedule():
    # Check subsets in order of largest to smallest
    for subset_size in range(len(friends), 0, -1):
        for subset in itertools.combinations(friends, subset_size):
            # Generate all permutations of this subset
            for perm in itertools.permutations(subset):
                meetings = is_valid_schedule(perm)
                if meetings is not None:
                    # Found a valid schedule
                    return {
                        "itinerary": meetings
                    }
    # If no schedule found (unlikely given the problem)
    return {"itinerary": []}

# Main execution
if __name__ == "__main__":
    schedule = find_optimal_schedule()
    print(json.dumps(schedule, indent=2))