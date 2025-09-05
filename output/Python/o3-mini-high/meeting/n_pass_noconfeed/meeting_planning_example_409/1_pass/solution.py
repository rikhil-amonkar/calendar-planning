import itertools
import json

def minutes_to_str(m):
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

# Input data for friends' meeting constraints (times in minutes since midnight)
friends = [
    {
        "name": "Thomas",
        "location": "Bayview",
        "avail_start": 15 * 60 + 30,  # 15:30 -> 930
        "avail_end": 18 * 60 + 30,    # 18:30 -> 1110
        "duration": 120
    },
    {
        "name": "Stephanie",
        "location": "Golden Gate Park",
        "avail_start": 18 * 60 + 30,  # 18:30 -> 1110
        "avail_end": 21 * 60 + 45,    # 21:45 -> 1305
        "duration": 30
    },
    {
        "name": "Laura",
        "location": "Nob Hill",
        "avail_start": 8 * 60 + 45,   # 8:45 -> 525
        "avail_end": 16 * 60 + 15,    # 16:15 -> 975
        "duration": 30
    },
    {
        "name": "Betty",
        "location": "Marina District",
        "avail_start": 18 * 60 + 45,  # 18:45 -> 1125
        "avail_end": 21 * 60 + 45,    # 21:45 -> 1305
        "duration": 45
    },
    {
        "name": "Patricia",
        "location": "Embarcadero",
        "avail_start": 17 * 60 + 30,  # 17:30 -> 1050
        "avail_end": 22 * 60 + 0,     # 22:00 -> 1320
        "duration": 45
    }
]

# Travel times in minutes between locations.
travel_times = {
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "Marina District"): 9,
    ("Fisherman's Wharf", "Embarcadero"): 8,

    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Golden Gate Park"): 22,
    ("Bayview", "Nob Hill"): 20,
    ("Bayview", "Marina District"): 25,
    ("Bayview", "Embarcadero"): 19,

    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Embarcadero"): 25,

    ("Nob Hill", "Fisherman's Wharf"): 11,
    ("Nob Hill", "Bayview"): 19,
    ("Nob Hill", "Golden Gate Park"): 17,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Embarcadero"): 9,

    ("Marina District", "Fisherman's Wharf"): 10,
    ("Marina District", "Bayview"): 27,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Embarcadero"): 14,

    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Bayview"): 21,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Marina District"): 12,
}

START_LOCATION = "Fisherman's Wharf"
START_TIME = 9 * 60  # 9:00 AM -> 540 minutes

def simulate_itinerary(order, start_time=START_TIME, start_location=START_LOCATION):
    """
    For a given order (permutation) of friend meetings, this function computes the earliest
    possible start and end times for each meeting subject to travel and individual constraints.
    It returns the itinerary (list of steps), the finishing time, and the count of meetings scheduled.
    """
    current_time = start_time
    current_location = start_location
    itinerary = []
    
    for friend in order:
        # Get travel time from current location to friend's meeting location.
        travel = travel_times.get((current_location, friend["location"]))
        if travel is None:
            # If no travel data, skip this friend.
            return itinerary, current_time, len(itinerary)
        
        arrival_time = current_time + travel
        # Wait if arriving before the friend is available.
        meeting_start = max(arrival_time, friend["avail_start"])
        meeting_end = meeting_start + friend["duration"]
        
        # Check if the meeting can be completed before the friend leaves.
        if meeting_end > friend["avail_end"]:
            # Cannot schedule this meeting; break out.
            break
        
        step = {
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": minutes_to_str(meeting_start),
            "end_time": minutes_to_str(meeting_end)
        }
        itinerary.append(step)
        current_time = meeting_end
        current_location = friend["location"]
    
    return itinerary, current_time, len(itinerary)

def find_best_itinerary(friends):
    best_itinerary = []
    best_finish_time = float('inf')
    best_count = 0
    
    # Try all permutations (orders) of the friends.
    for order in itertools.permutations(friends):
        itinerary, finish_time, count = simulate_itinerary(order)
        # Primary goal: maximize number of meetings
        # Secondary: choose itinerary that finishes earlier
        if count > best_count or (count == best_count and finish_time < best_finish_time):
            best_itinerary = itinerary
            best_finish_time = finish_time
            best_count = count
            
    return best_itinerary, best_count, best_finish_time

def main():
    best_itinerary, count, finish_time = find_best_itinerary(friends)
    output = {
        "itinerary": best_itinerary
    }
    print(json.dumps(output, indent=2))

if __name__ == '__main__':
    main()