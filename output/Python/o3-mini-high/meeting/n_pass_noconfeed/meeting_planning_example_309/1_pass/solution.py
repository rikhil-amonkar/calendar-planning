import json
import itertools

# Helper function: convert minutes since midnight to a string in "H:MM" format (24-hour, no leading zero for hour)
def format_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

# Input parameters

# Starting point and time (Financial District at 9:00AM)
start_location = "Financial District"
start_time = 9 * 60  # 9:00 AM in minutes

# Travel times dictionary (in minutes)
travel_times = {
    ("Financial District", "Chinatown"): 5,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Bayview"): 19,
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Chinatown", "Financial District"): 5,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Bayview"): 22,
    ("Chinatown", "Fisherman's Wharf"): 8,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Chinatown"): 16,
    ("Alamo Square", "Bayview"): 16,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Bayview", "Financial District"): 19,
    ("Bayview", "Chinatown"): 18,
    ("Bayview", "Alamo Square"): 16,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Alamo Square"): 20,
    ("Fisherman's Wharf", "Bayview"): 26
}

# Meeting constraints for each friend
# Times are in minutes since midnight. e.g., 9:30AM = 570 minutes.
friends = [
    {
        "name": "Nancy",
        "location": "Chinatown",
        "available_start": 9 * 60 + 30,   # 9:30 AM = 570 minutes
        "available_end": 13 * 60 + 30,      # 1:30 PM = 810 minutes
        "min_duration": 90
    },
    {
        "name": "Mary",
        "location": "Alamo Square",
        "available_start": 7 * 60,          # 7:00 AM = 420 minutes
        "available_end": 21 * 60,           # 9:00 PM = 1260 minutes
        "min_duration": 75
    },
    {
        "name": "Jessica",
        "location": "Bayview",
        "available_start": 11 * 60 + 15,    # 11:15 AM = 675 minutes
        "available_end": 13 * 60 + 45,      # 1:45 PM = 825 minutes
        "min_duration": 45
    },
    {
        "name": "Rebecca",
        "location": "Fisherman's Wharf",
        "available_start": 7 * 60,          # 7:00 AM = 420 minutes
        "available_end": 8 * 60 + 30,       # 8:30 AM = 510 minutes
        "min_duration": 45
    }
]

# We want to maximize the number of friends met. We'll check all possible subsets
def compute_itinerary(order):
    itinerary = []
    current_time = start_time
    current_location = start_location

    for friend in order:
        # Get travel time from current_location to friend's meeting location.
        travel_key = (current_location, friend["location"])
        if travel_key not in travel_times:
            # If no travel time exists between these locations, itinerary invalid.
            return None, None
        travel_time = travel_times[travel_key]
        arrival_time = current_time + travel_time

        # Meeting cannot start before the friend is available.
        meeting_start = max(arrival_time, friend["available_start"])
        meeting_end = meeting_start + friend["min_duration"]

        # Check if meeting finishes before the friend leaves.
        if meeting_end > friend["available_end"]:
            return None, None

        # Append meeting details to itinerary.
        itinerary.append({
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": format_time(meeting_start),
            "end_time": format_time(meeting_end)
        })

        # Update current time and location for the next meeting.
        current_time = meeting_end
        current_location = friend["location"]

    return itinerary, current_time

# We'll search for the schedule that meets the maximum number of friends,
# and among those, pick the one that finishes earliest.
best_schedule = None
best_count = 0
best_finish_time = None

# Check all subsets (all lengths) of friends.
n = len(friends)
# We'll generate combinations of all possible sizes.
for r in range(1, n + 1):
    for subset in itertools.combinations(friends, r):
        # For each ordering (permutation) of this subset.
        for order in itertools.permutations(subset):
            schedule, finish_time = compute_itinerary(order)
            if schedule is not None:
                count = len(schedule)
                # If this schedule meets more friends than the best so far,
                # or if equal count and finishes earlier, update best_schedule.
                if count > best_count or (count == best_count and (best_finish_time is None or finish_time < best_finish_time)):
                    best_schedule = schedule
                    best_count = count
                    best_finish_time = finish_time

# Our goal is to maximize the number of meetings.
# In our constraints, Rebecca is not reachable because we arrive at 9:00.
# Thus, an optimal schedule will likely include Nancy, Mary, and Jessica.
result = {"itinerary": best_schedule if best_schedule is not None else []}
print(json.dumps(result, indent=2))