import json
import itertools

# Helper functions
def minutes_to_time(m):
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

def simulate_schedule(departure, perm, travel):
    """
    Given a departure time (in minutes) from the starting location,
    and an ordering (perm) of friend meetings, simulate the schedule.
    Returns a tuple (finish_time, total_friend_wait, schedule)
    if the schedule is feasible; otherwise returns None.
    """
    schedule = []
    total_friend_wait = 0
    current_time = departure
    current_loc = "Fisherman's Wharf"
    
    for friend in perm:
        # Travel from current location to friend's location
        key = (current_loc, friend["location"])
        if key not in travel:
            return None  # Should not happen if all travel times defined
        travel_time = travel[key]
        arrival = current_time + travel_time
        # Meeting cannot start until friend is available.
        meeting_start = max(arrival, friend["avail_start"])
        wait = meeting_start - arrival
        total_friend_wait += wait
        meeting_end = meeting_start + friend["min_duration"]
        if meeting_end > friend["avail_end"]:
            return None   # Infeasible because meeting would run past available time.
        # Save meeting details (times in minutes)
        meeting = {
            "person": friend["name"],
            "location": friend["location"],
            "start": meeting_start,
            "end": meeting_end
        }
        schedule.append(meeting)
        # Update current time and location (after meeting)
        current_time = meeting_end
        current_loc = friend["location"]
    
    # Overall finish time is the end time of the last meeting.
    return current_time, total_friend_wait, schedule

# Input Parameters

# Define travel times in minutes (directional)
travel_times = {
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Richmond District"): 7,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Presidio"): 7
}

# Friend meeting constraints:
friends = [
    {
        "name": "Melissa",
        "location": "Golden Gate Park",
        # Available from 8:30AM (510) to 8:00PM (1200)
        "avail_start": 8 * 60 + 30,
        "avail_end": 20 * 60,
        "min_duration": 15
    },
    {
        "name": "Nancy",
        "location": "Presidio",
        # Available from 7:45PM (1185) to 10:00PM (1320)
        "avail_start": 19 * 60 + 45,
        "avail_end": 22 * 60,
        "min_duration": 105
    },
    {
        "name": "Emily",
        "location": "Richmond District",
        # Available from 4:45PM (1005) to 10:00PM (1320)
        "avail_start": 16 * 60 + 45,
        "avail_end": 22 * 60,
        "min_duration": 120
    }
]

# You arrive at Fisherman's Wharf at 9:00AM (540 minutes)
start_time = 9 * 60  # 540 minutes

# Search for an optimal schedule.
# We consider all orderings (permutations) of the friend meetings and vary the departure time d0 from home.
best_schedule = None
# Cost is a tuple: (finish_time, total_friend_wait, departure) - lower is better.
best_cost = (float('inf'), float('inf'), float('inf'))

# We'll try departure times from start_time to an upper bound.
# Since friends finish by at most about 22:00, we can try departures up to, say, 1200 minutes.
for perm in itertools.permutations(friends):
    # For each permutation, iterate possible departure times from your starting point.
    for d0 in range(start_time, 1200):
        sim = simulate_schedule(d0, perm, travel_times)
        if sim is None:
            continue
        finish_time, friend_wait, sched = sim
        # We require that the schedule finish by the latest available time of the last meeting.
        # Our objective is to finish as early as possible and minimize waiting time with friends.
        cost = (finish_time, friend_wait, d0)
        if cost < best_cost:
            best_cost = cost
            best_schedule = {
                "departure": d0,
                "perm": perm,
                "schedule": sched
            }

# If no schedule is found, output an empty itinerary.
if best_schedule is None:
    result = {"itinerary": []}
else:
    # Convert meeting times (in minutes) to "H:MM" format.
    itinerary = []
    for meeting in best_schedule["schedule"]:
        item = {
            "action": "meet",
            "location": meeting["location"],
            "person": meeting["person"],
            "start_time": minutes_to_time(meeting["start"]),
            "end_time": minutes_to_time(meeting["end"])
        }
        itinerary.append(item)
    result = {"itinerary": itinerary}

# Output the result as JSON-formatted string.
print(json.dumps(result, indent=2))