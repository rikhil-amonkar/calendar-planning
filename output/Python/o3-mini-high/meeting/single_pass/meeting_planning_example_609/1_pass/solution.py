#!/usr/bin/env python3
import json
import itertools

def minutes_to_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

# Travel times between locations (in minutes)
travel_times = {
    ("Chinatown", "Mission District"): 18,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "Presidio"): 19,
    ("Mission District", "Chinatown"): 16,
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Union Square"): 15,
    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "Sunset District"): 24,
    ("Mission District", "Presidio"): 25,
    ("Alamo Square", "Chinatown"): 16,
    ("Alamo Square", "Mission District"): 10,
    ("Alamo Square", "Pacific Heights"): 10,
    ("Alamo Square", "Union Square"): 14,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Presidio"): 18,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Sunset District"): 21,
    ("Pacific Heights", "Presidio"): 11,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Mission District"): 14,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Sunset District"): 26,
    ("Union Square", "Presidio"): 24,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "Alamo Square"): 10,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Presidio"): 11,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Mission District"): 24,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Pacific Heights"): 21,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Presidio"): 16,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Mission District"): 26,
    ("Presidio", "Alamo Square"): 18,
    ("Presidio", "Pacific Heights"): 11,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Sunset District"): 15,
}

# Define friend meeting constraints.
# Times are represented in minutes after midnight.
# For example, 9:00 AM is 9*60 = 540.
friends = [
    {"name": "David", "location": "Mission District", "avail_start": 8*60, "avail_end": 19*60+45, "duration": 45},
    {"name": "Kenneth", "location": "Alamo Square", "avail_start": 14*60, "avail_end": 19*60+45, "duration": 120},
    {"name": "John", "location": "Pacific Heights", "avail_start": 17*60, "avail_end": 20*60, "duration": 15},
    {"name": "Charles", "location": "Union Square", "avail_start": 21*60+45, "avail_end": 22*60+45, "duration": 60},
    {"name": "Deborah", "location": "Golden Gate Park", "avail_start": 7*60, "avail_end": 18*60+15, "duration": 90},
    {"name": "Karen", "location": "Sunset District", "avail_start": 17*60+45, "avail_end": 21*60+15, "duration": 15},
    {"name": "Carol", "location": "Presidio", "avail_start": 8*60+15, "avail_end": 9*60+15, "duration": 30},
]

# You arrive at Chinatown at 9:00 AM.
start_time = 9 * 60  # 9:00 in minutes after midnight
start_location = "Chinatown"

def simulate_schedule(order):
    current_time = start_time
    current_location = start_location
    itinerary = []
    for friend in order:
        # Get travel time from current location to the friend's location.
        travel = travel_times.get((current_location, friend["location"]))
        if travel is None:
            continue
        arrival_time = current_time + travel
        meeting_start = max(arrival_time, friend["avail_start"])
        meeting_end = meeting_start + friend["duration"]
        # Check if the meeting can be held within the friend's available window.
        if meeting_end <= friend["avail_end"]:
            itinerary.append({
                "action": "meet",
                "location": friend["location"],
                "person": friend["name"],
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            })
            current_time = meeting_end
            current_location = friend["location"]
    return itinerary, len(itinerary), current_time

def find_best_itinerary():
    best_itinerary = []
    best_count = -1
    best_finish = float('inf')
    # Try all possible orders of meetings.
    for perm in itertools.permutations(friends):
        itin, count, finish_time = simulate_schedule(perm)
        # Choose the itinerary with the maximum number of meetings.
        # In a tie, choose the one that finishes earliest.
        if count > best_count or (count == best_count and finish_time < best_finish):
            best_itinerary = itin
            best_count = count
            best_finish = finish_time
    return best_itinerary

def main():
    best_itin = find_best_itinerary()
    result = {"itinerary": best_itin}
    print(json.dumps(result))

if __name__ == "__main__":
    main()