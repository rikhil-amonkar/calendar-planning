#!/usr/bin/env python3
import itertools
import json

# Convert a time in minutes (since midnight) to "H:MM" 24-hour format.
def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

# Define the travel times (in minutes) as provided.
# Keys are tuples: (origin, destination)
travel_times = {
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Bayview"): 15,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Russian Hill"): 15,
    ("Mission District", "Fisherman's Wharf"): 22,
    
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Mission District"): 13,
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "Russian Hill"): 23,
    ("Bayview", "Fisherman's Wharf"): 25,
    
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Bayview"): 22,
    ("Pacific Heights", "Russian Hill"): 7,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Mission District"): 16,
    ("Russian Hill", "Bayview"): 23,
    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "Russian Hill"): 7,
}

# Define the meeting constraints for each friend.
# Times are stored in minutes since midnight.
# For example, 9:00 AM is 9*60 = 540.
friends = [
    {
        "name": "Stephanie",
        "location": "Mission District",
        "avail_start": 8*60 + 15,   # 8:15
        "avail_end": 13*60 + 45,    # 13:45
        "duration": 90             # minutes needed
    },
    {
        "name": "Sandra",
        "location": "Bayview",
        "avail_start": 13*60,       # 13:00
        "avail_end": 19*60 + 30,    # 19:30
        "duration": 15             # minutes needed
    },
    {
        "name": "Richard",
        "location": "Pacific Heights",
        "avail_start": 7*60 + 15,   # 7:15
        "avail_end": 10*60 + 15,    # 10:15
        "duration": 75             # minutes needed
    },
    {
        "name": "Brian",
        "location": "Russian Hill",
        "avail_start": 12*60 + 15,  # 12:15
        "avail_end": 16*60,         # 16:00
        "duration": 120            # minutes needed
    },
    {
        "name": "Jason",
        "location": "Fisherman's Wharf",
        "avail_start": 8*60 + 30,   # 8:30
        "avail_end": 17*60 + 45,    # 17:45
        "duration": 60             # minutes needed
    }
]

# Our starting location and arrival time.
start_location = "Haight-Ashbury"
start_time = 9 * 60  # 9:00 AM in minutes

# Function to simulate a meeting itinerary for a given ordered list of friends.
# Returns a tuple: (number_of_meetings, finish_time, itinerary_list)
# If a meeting in the ordered list is not feasible, the simulation stops and returns the count for the valid prefix.
def simulate_itinerary(order):
    current_time = start_time
    current_location = start_location
    itinerary = []
    for friend in order:
        # Get travel time from current location to friend's meeting location.
        travel_key = (current_location, friend["location"])
        if travel_key not in travel_times:
            # In case no travel time is defined, consider it not feasible.
            return (len(itinerary), current_time, itinerary)
        travel_time = travel_times[travel_key]
        arrival_time = current_time + travel_time
        # The meeting can start no earlier than the friend’s available start.
        meeting_start = max(arrival_time, friend["avail_start"])
        meeting_end = meeting_start + friend["duration"]
        # Check if meeting end is within friend's available window.
        if meeting_end > friend["avail_end"]:
            # This ordering cannot schedule this friend meeting.
            return (len(itinerary), current_time, itinerary)
        # Add the meeting to the itinerary.
        itinerary.append({
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        })
        # Update current time and location for the next meeting.
        current_time = meeting_end
        current_location = friend["location"]
    return (len(itinerary), current_time, itinerary)

def get_all_subsets(items):
    # Returns all non-empty subsets of the list 'items'
    all_subsets = []
    for r in range(1, len(items) + 1):
        for subset in itertools.combinations(items, r):
            all_subsets.append(list(subset))
    return all_subsets

def main():
    best_count = -1
    best_finish = float('inf')
    best_itinerary = []
    
    subsets = get_all_subsets(friends)
    # For each subset, check every permutation ordering.
    for subset in subsets:
        for perm in itertools.permutations(subset):
            count, finish, itinerary = simulate_itinerary(perm)
            # We want the maximum number of meetings; if tie, the itinerary finishing earlier is better.
            if count > best_count or (count == best_count and finish < best_finish):
                best_count = count
                best_finish = finish
                best_itinerary = itinerary

    result = {
        "itinerary": best_itinerary
    }
    # Output the result as a JSON-formatted dictionary.
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()