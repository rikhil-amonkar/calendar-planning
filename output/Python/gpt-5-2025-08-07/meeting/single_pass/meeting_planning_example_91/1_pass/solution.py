import json
from itertools import permutations

def parse_time(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def earliest_feasible_start(current_time, current_loc, friend, travel_times):
    # Compute travel time
    if current_loc == friend["location"]:
        travel = 0
    else:
        travel = travel_times.get((current_loc, friend["location"]), None)
        if travel is None:
            return None  # No route
    arrival = current_time + travel
    avail_start = parse_time(friend["available_start"])
    avail_end = parse_time(friend["available_end"])
    min_meet = friend["min_meet_minutes"]
    # We can only start at or after both arrival and availability start
    start = max(arrival, avail_start)
    # Need to ensure we can meet for at least min_meet within availability window
    if start + min_meet <= avail_end:
        return start
    return None

def plan_itinerary(friends, start_location, start_time, travel_times):
    # Try all permutations to "consider various different schedules" and pick best by count, then earliest finish
    best_itin = []
    best_finish = None
    for order in permutations(friends):
        current_loc = start_location
        current_time = parse_time(start_time)
        itinerary = []
        for fr in order:
            start = earliest_feasible_start(current_time, current_loc, fr, travel_times)
            if start is None:
                continue
            # Schedule exactly minimum required meeting duration to maximize potential for more meetings
            end = start + fr["min_meet_minutes"]
            # Record meeting
            itinerary.append({
                "action": "meet",
                "location": fr["location"],
                "person": fr["name"],
                "start_time": fmt_time(start),
                "end_time": fmt_time(end),
            })
            # Update state
            current_loc = fr["location"]
            current_time = end
        # Evaluate this itinerary
        if len(itinerary) > len(best_itin):
            best_itin = itinerary
            best_finish = current_time if itinerary else None
        elif len(itinerary) == len(best_itin) and len(itinerary) > 0:
            # Tie-breaker: earlier finish time
            if best_finish is None or current_time < best_finish:
                best_itin = itinerary
                best_finish = current_time
    return best_itin

def main():
    # Input variables (as specified)
    arrival_location = "Russian Hill"
    arrival_time = "9:00"
    travel_times = {
        ("Russian Hill", "Richmond District"): 14,
        ("Richmond District", "Russian Hill"): 13,
    }
    friends = [
        {
            "name": "Daniel",
            "location": "Richmond District",
            "available_start": "19:00",
            "available_end": "20:15",
            "min_meet_minutes": 75,
        }
    ]

    itinerary = plan_itinerary(friends, arrival_location, arrival_time, travel_times)
    output = {"itinerary": itinerary}
    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()