import itertools
import json

# Convert time in minutes (since midnight) to string in H:MM 24-hr format.
def minutes_to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Meeting constraints data (times in minutes since midnight)
# Joseph: available 8:30 (510) to 19:15 (1155), duration 60
# Nancy: available 11:00 (660) to 16:00 (960), duration 90
# Jason: available 16:45 (1005) to 21:45 (1305), duration 15
# Jeffrey: available 10:30 (630) to 15:45 (945), duration 45
meetings = [
    {
        "person": "Joseph",
        "location": "Russian Hill",
        "available_start": 510,
        "available_end": 1155,
        "duration": 60
    },
    {
        "person": "Nancy",
        "location": "Alamo Square",
        "available_start": 660,
        "available_end": 960,
        "duration": 90
    },
    {
        "person": "Jason",
        "location": "North Beach",
        "available_start": 1005,
        "available_end": 1305,
        "duration": 15
    },
    {
        "person": "Jeffrey",
        "location": "Financial District",
        "available_start": 630,
        "available_end": 945,
        "duration": 45
    }
]

# Travel times (in minutes) between locations.
travel_times = {
    "Bayview": {
        "Russian Hill": 23,
        "Alamo Square": 16,
        "North Beach": 21,
        "Financial District": 19
    },
    "Russian Hill": {
        "Bayview": 23,
        "Alamo Square": 15,
        "North Beach": 5,
        "Financial District": 11
    },
    "Alamo Square": {
        "Bayview": 16,
        "Russian Hill": 13,
        "North Beach": 15,
        "Financial District": 17
    },
    "North Beach": {
        "Bayview": 22,
        "Russian Hill": 4,
        "Alamo Square": 16,
        "Financial District": 8
    },
    "Financial District": {
        "Bayview": 19,
        "Russian Hill": 10,
        "Alamo Square": 17,
        "North Beach": 7
    }
}

# Starting location and time (9:00AM = 540 minutes)
START_LOCATION = "Bayview"
START_TIME = 540

# Simulate a schedule for a given ordering of meetings.
# Returns a tuple: (count, itinerary, total_wait, finish_time)
def simulate_schedule(order, start_location, start_time):
    itinerary = []
    current_time = start_time
    current_location = start_location
    total_wait = 0
    count = 0

    for meeting in order:
        # Travel from current_location to next meeting location
        travel = travel_times[current_location][meeting["location"]]
        arrival_time = current_time + travel
        
        # The meeting can only start when the friend is available.
        meeting_start = max(arrival_time, meeting["available_start"])
        wait_time = meeting_start - arrival_time
        meeting_end = meeting_start + meeting["duration"]
        
        # Check if meeting can be completed before the friend's availability ends.
        if meeting_end > meeting["available_end"]:
            # Cannot schedule this meeting, break out and return what we have.
            break
        
        # Record itinerary item.
        itinerary.append({
            "action": "meet",
            "location": meeting["location"],
            "person": meeting["person"],
            "start_time": minutes_to_time_str(meeting_start),
            "end_time": minutes_to_time_str(meeting_end)
        })
        count += 1
        total_wait += wait_time
        current_time = meeting_end
        current_location = meeting["location"]
    
    return count, itinerary, total_wait, current_time

def main():
    best_schedule = None
    best_count = -1
    best_total_wait = float('inf')
    best_finish = float('inf')
    
    # Try every permutation (order) of meetings.
    for order in itertools.permutations(meetings):
        count, itinerary, total_wait, finish_time = simulate_schedule(order, START_LOCATION, START_TIME)
        # We want to maximize count (number of meetings), then minimize waiting and finishing time.
        # Only consider the schedule if it has at least as many meetings as the best found.
        if count > best_count:
            best_count = count
            best_total_wait = total_wait
            best_finish = finish_time
            best_schedule = itinerary
        elif count == best_count:
            if total_wait < best_total_wait:
                best_total_wait = total_wait
                best_finish = finish_time
                best_schedule = itinerary
            elif total_wait == best_total_wait and finish_time < best_finish:
                best_finish = finish_time
                best_schedule = itinerary

    result = {
        "itinerary": best_schedule if best_schedule is not None else []
    }
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()