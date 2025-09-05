import json
import itertools

def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def compute_schedule(order, start_time, start_location, travel_times):
    itinerary = []
    current_time = start_time
    current_location = start_location
    for friend in order:
        # Calculate travel time to the friend's location
        travel_time = travel_times[(current_location, friend["location"])]
        arrival_time = current_time + travel_time
        # Start meeting when both you and the friend are available
        meeting_start = max(arrival_time, friend["avail_start"])
        meeting_end = meeting_start + friend["min_duration"]
        # Check if the meeting can finish before the friend leaves
        if meeting_end > friend["avail_end"]:
            return None  # This ordering is not feasible.
        itinerary.append({
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": to_time_str(meeting_start),
            "end_time": to_time_str(meeting_end)
        })
        current_time = meeting_end
        current_location = friend["location"]
    return itinerary, current_time

def main():
    # Start parameters: arriving at Nob Hill at 9:00 AM (9*60 = 540 minutes from midnight)
    start_time = 9 * 60  # 540 minutes
    start_location = "Nob Hill"
    
    # Friend meeting constraints:
    # Thomas is at Pacific Heights from 15:30 to 19:15 and requires 75 minutes.
    # Kenneth is at Mission District from 12:00 to 15:45 and requires 45 minutes.
    friends = [
        {
            "name": "Thomas",
            "location": "Pacific Heights",
            "avail_start": 15 * 60 + 30,   # 15:30 -> 930 minutes
            "avail_end": 19 * 60 + 15,     # 19:15 -> 1155 minutes
            "min_duration": 75
        },
        {
            "name": "Kenneth",
            "location": "Mission District",
            "avail_start": 12 * 60,        # 12:00 -> 720 minutes
            "avail_end": 15 * 60 + 45,     # 15:45 -> 945 minutes
            "min_duration": 45
        }
    ]
    
    # Travel times (in minutes) between locations
    travel_times = {
        ("Nob Hill", "Pacific Heights"): 8,
        ("Nob Hill", "Mission District"): 13,
        ("Pacific Heights", "Nob Hill"): 8,
        ("Pacific Heights", "Mission District"): 15,
        ("Mission District", "Nob Hill"): 12,
        ("Mission District", "Pacific Heights"): 16
    }
    
    # Try all orders of meeting the friends and choose the schedule that meets the most friends.
    best_itinerary = None
    best_meetings_count = 0
    best_finish_time = float('inf')
    
    for order in itertools.permutations(friends):
        result = compute_schedule(order, start_time, start_location, travel_times)
        if result is not None:
            itinerary, finish_time = result
            count = len(itinerary)
            if count > best_meetings_count or (count == best_meetings_count and finish_time < best_finish_time):
                best_itinerary = itinerary
                best_meetings_count = count
                best_finish_time = finish_time

    result_json = {
        "itinerary": best_itinerary if best_itinerary is not None else []
    }
    
    print(json.dumps(result_json, indent=2))

if __name__ == "__main__":
    main()