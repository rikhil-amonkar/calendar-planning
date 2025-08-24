import json

def to_minutes(time_str):
    # Expects formats like '9:00' or '13:30' (no leading zero needed)
    h, m = time_str.split(":")
    return int(h) * 60 + int(m)

def to_time_str(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def best_meeting_with_single_friend(arrival_loc, arrival_time_min, friend, travel_times, min_meet_minutes):
    """
    Compute the best meeting interval for a single friend, considering all feasible departure times.
    Optimization: maximize meeting duration; tie-breaker: minimize waiting time at meeting location.
    """
    friend_name = friend["name"]
    friend_loc = friend["location"]
    friend_start = friend["start"]
    friend_end = friend["end"]

    # If there is no travel time defined between current location and friend's location, cannot meet
    if (arrival_loc, friend_loc) not in travel_times:
        return None

    travel_time = travel_times[(arrival_loc, friend_loc)]

    # Enumerate possible departure times from the arrival location to consider different schedules
    latest_departure = friend_end - travel_time
    if latest_departure < arrival_time_min:
        return None

    best = None  # (meeting_duration, -wait_time, depart_time, meet_start, meet_end)

    # Note: enumerating minute-by-minute ensures we "consider various different schedules"
    for depart_time in range(arrival_time_min, latest_departure + 1):
        arrive_time = depart_time + travel_time
        # Meeting can only start when both you and the friend are present
        meet_start = max(arrive_time, friend_start)
        meet_end = friend_end
        if meet_start >= meet_end:
            continue
        duration = meet_end - meet_start
        if duration < min_meet_minutes:
            continue
        wait_time = max(0, friend_start - arrive_time)
        candidate = (duration, -wait_time, depart_time, meet_start, meet_end)
        if best is None or candidate > best:
            best = candidate

    if best is None:
        return None

    _, _, chosen_depart, meet_start, meet_end = best
    return {
        "person": friend_name,
        "location": friend_loc,
        "start_time": to_time_str(meet_start),
        "end_time": to_time_str(meet_end),
        "depart_time": to_time_str(chosen_depart)  # internal use; not output in itinerary
    }

def main():
    # INPUT VARIABLES (from problem statement)
    arrival_location = "Sunset District"
    arrival_time_str = "9:00"
    travel_times = {
        ("Sunset District", "Golden Gate Park"): 11,
        ("Golden Gate Park", "Sunset District"): 10
    }

    friends = [
        {
            "name": "Joshua",
            "location": "Golden Gate Park",
            "start": "20:45",
            "end": "21:45"
        }
    ]

    min_meet_minutes = 15

    # Convert inputs to minutes
    arrival_time_min = to_minutes(arrival_time_str)
    for f in friends:
        f["start"] = to_minutes(f["start"])
        f["end"] = to_minutes(f["end"])

    # Since there is only one friend, we simply compute the best feasible meeting with that friend.
    # The framework below is written to be extendable for multiple friends.
    itinerary = []
    for f in friends:
        res = best_meeting_with_single_friend(arrival_location, arrival_time_min, f, travel_times, min_meet_minutes)
        if res:
            itinerary.append({
                "action": "meet",
                "location": res["location"],
                "person": res["person"],
                "start_time": res["start_time"],
                "end_time": res["end_time"]
            })

    output = {"itinerary": itinerary}
    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()