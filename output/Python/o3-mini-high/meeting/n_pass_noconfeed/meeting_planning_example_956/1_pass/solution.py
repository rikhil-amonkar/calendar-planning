#!/usr/bin/env python3
import json

# Helper function: convert minutes since midnight to "H:MM" format.
def minutes_to_time(m):
    h = m // 60
    m_rem = m % 60
    return f"{h}:{m_rem:02d}"

# Define the friends' meeting constraints.
# Times are given in minutes after midnight.
# For example, 9:00 AM is 9*60 = 540.
friends = [
    {
        "name": "William",
        "location": "Alamo Square",
        "avail_start": 15 * 60 + 15,  # 15:15 -> 915
        "avail_end": 17 * 60 + 15,    # 17:15 -> 1035
        "duration": 60
    },
    {
        "name": "Joshua",
        "location": "Richmond District",
        "avail_start": 7 * 60 + 0,    # 7:00 -> 420
        "avail_end": 20 * 60 + 0,     # 20:00 -> 1200
        "duration": 15
    },
    {
        "name": "Joseph",
        "location": "Financial District",
        "avail_start": 11 * 60 + 15,  # 11:15 -> 675
        "avail_end": 13 * 60 + 30,    # 13:30 -> 810
        "duration": 15
    },
    {
        "name": "David",
        "location": "Union Square",
        "avail_start": 16 * 60 + 45,  # 16:45 -> 1005
        "avail_end": 19 * 60 + 15,    # 19:15 -> 1155
        "duration": 45
    },
    {
        "name": "Brian",
        "location": "Fisherman's Wharf",
        "avail_start": 13 * 60 + 45,  # 13:45 -> 825
        "avail_end": 20 * 60 + 45,    # 20:45 -> 1245
        "duration": 105
    },
    {
        "name": "Karen",
        "location": "Marina District",
        "avail_start": 11 * 60 + 30,  # 11:30 -> 690
        "avail_end": 18 * 60 + 30,    # 18:30 -> 1110
        "duration": 15
    },
    {
        "name": "Anthony",
        "location": "Haight-Ashbury",
        "avail_start": 7 * 60 + 15,   # 7:15 -> 435
        "avail_end": 10 * 60 + 30,    # 10:30 -> 630
        "duration": 30
    },
    {
        "name": "Matthew",
        "location": "Mission District",
        "avail_start": 17 * 60 + 15,  # 17:15 -> 1035
        "avail_end": 19 * 60 + 15,    # 19:15 -> 1155
        "duration": 120
    },
    {
        "name": "Helen",
        "location": "Pacific Heights",
        "avail_start": 8 * 60 + 0,    # 8:00 -> 480
        "avail_end": 12 * 60 + 0,     # 12:00 -> 720
        "duration": 75
    },
    {
        "name": "Jeffrey",
        "location": "Golden Gate Park",
        "avail_start": 19 * 60 + 0,   # 19:00 -> 1140
        "avail_end": 21 * 60 + 30,    # 21:30 -> 1290
        "duration": 60
    }
]

# Define the travel times (in minutes) between locations.
# The keys are tuples: (origin, destination)
travel = {
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Financial District"): 21,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "Fisherman's Wharf"): 24,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Haight-Ashbury"): 6,
    ("The Castro", "Mission District"): 7,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Golden Gate Park"): 11,

    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Richmond District"): 11,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Union Square"): 14,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "Haight-Ashbury"): 5,
    ("Alamo Square", "Mission District"): 10,
    ("Alamo Square", "Pacific Heights"): 10,
    ("Alamo Square", "Golden Gate Park"): 9,

    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Alamo Square"): 13,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "Union Square"): 21,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "Mission District"): 20,
    ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "Golden Gate Park"): 9,

    ("Financial District", "The Castro"): 20,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "Mission District"): 17,
    ("Financial District", "Pacific Heights"): 13,
    ("Financial District", "Golden Gate Park"): 23,

    ("Union Square", "The Castro"): 17,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Richmond District"): 20,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "Mission District"): 14,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "Golden Gate Park"): 22,

    ("Fisherman's Wharf", "The Castro"): 27,
    ("Fisherman's Wharf", "Alamo Square"): 21,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Fisherman's Wharf", "Union Square"): 13,
    ("Fisherman's Wharf", "Marina District"): 9,
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,

    ("Marina District", "The Castro"): 22,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Fisherman's Wharf"): 10,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Mission District"): 20,
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "Golden Gate Park"): 18,

    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "Richmond District"): 10,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "Golden Gate Park"): 7,

    ("Mission District", "The Castro"): 7,
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "Richmond District"): 20,
    ("Mission District", "Financial District"): 15,
    ("Mission District", "Union Square"): 15,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Mission District", "Marina District"): 19,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Golden Gate Park"): 17,

    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Richmond District"): 12,
    ("Pacific Heights", "Financial District"): 13,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Golden Gate Park"): 15,

    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Alamo Square"): 9,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "Pacific Heights"): 16,
}

# Use recursion with memoization to search through possible meeting orders.
# We want to maximize the number of friends we meet.
# state: (current_time, current_location, mask)
# mask is a bitmask of which friends have been met.
memo = {}

def search(current_time, current_loc, mask):
    key = (mask, current_loc, current_time)
    if key in memo:
        return memo[key]
    best_count = 0
    best_schedule = []
    n = len(friends)
    # Try each friend that has not yet been visited.
    for i in range(n):
        if not (mask & (1 << i)):
            friend = friends[i]
            # Get travel time from the current location to friend's location.
            travel_time = travel.get((current_loc, friend["location"]))
            if travel_time is None:
                # Fallback: try reversed (should not occur with our complete dataset)
                travel_time = travel.get((friend["location"], current_loc))
                if travel_time is None:
                    continue
            arrival = current_time + travel_time
            # Wait if arriving before friend's availability start.
            start_meet = max(arrival, friend["avail_start"])
            end_meet = start_meet + friend["duration"]
            # Check if meeting can finish within the friend’s available window.
            if end_meet <= friend["avail_end"]:
                # Recurse from the new location and time.
                next_count, next_schedule = search(end_meet, friend["location"], mask | (1 << i))
                candidate = 1 + next_count
                if candidate > best_count:
                    best_count = candidate
                    event = {
                        "action": "meet",
                        "location": friend["location"],
                        "person": friend["name"],
                        "start_time": minutes_to_time(start_meet),
                        "end_time": minutes_to_time(end_meet)
                    }
                    best_schedule = [event] + next_schedule
    memo[key] = (best_count, best_schedule)
    return memo[key]

# Starting parameters: arrive at "The Castro" at 9:00 AM (540 minutes)
start_time = 9 * 60  # 540
start_location = "The Castro"
_, itinerary = search(start_time, start_location, 0)

# Prepare the output JSON dictionary.
result = {"itinerary": itinerary}

# Output the result as JSON.
print(json.dumps(result, indent=2))