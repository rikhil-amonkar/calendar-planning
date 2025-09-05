"SOLUTION:"
import json
from itertools import permutations

def to_minutes(hm):
    # hm like '9:00' or '20:45'
    parts = hm.split(":")
    h = int(parts[0])
    m = int(parts[1])
    return h * 60 + m

def to_hm(m):
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

class Friend:
    def __init__(self, name, location, window_start_hm, window_end_hm, min_duration_min):
        self.name = name
        self.location = location
        self.window_start = to_minutes(window_start_hm)
        self.window_end = to_minutes(window_end_hm)
        self.min_duration = min_duration_min

def compute_best_schedule(start_location, start_time_hm, travel_times, friends):
    start_time = to_minutes(start_time_hm)
    # build a lookup for travel time; if not present, treat as impossible (None)
    def travel_time(from_loc, to_loc):
        return travel_times.get((from_loc, to_loc), None)

    best = {
        "count": -1,
        "total_duration": -1,
        "itinerary": []
    }

    # Explore all permutations and optional skipping of friends via DFS
    def dfs(order, idx, cur_loc, cur_time, current_itinerary, total_duration):
        nonlocal best

        # if we've considered all friends in this order, check if best
        if idx == len(order):
            cur_count = len(current_itinerary)
            if (cur_count > best["count"]) or (cur_count == best["count"] and total_duration > best["total_duration"]):
                best = {
                    "count": cur_count,
                    "total_duration": total_duration,
                    "itinerary": list(current_itinerary)
                }
            return

        fr = order[idx]

        # Option 1: Try to meet this friend
        t = travel_time(cur_loc, fr.location)
        if t is not None:
            earliest_arrival = cur_time + t
            # Meeting can only start when both are present
            meet_start = max(earliest_arrival, fr.window_start)
            # If we can arrive before window starts, we can wait until window_start
            # Meeting can go until friend leaves
            meet_end = fr.window_end
            duration = meet_end - meet_start
            if duration >= fr.min_duration and meet_start < meet_end:
                # Meeting is feasible; add to itinerary and continue
                current_itinerary.append({
                    "action": "meet",
                    "location": fr.location,
                    "person": fr.name,
                    "start_time": to_hm(meet_start),
                    "end_time": to_hm(meet_end)
                })
                dfs(order, idx + 1, fr.location, meet_end, current_itinerary, total_duration + duration)
                current_itinerary.pop()

        # Option 2: Skip this friend
        dfs(order, idx + 1, cur_loc, cur_time, current_itinerary, total_duration)

    # Explore all friend orders
    for order in permutations(friends):
        dfs(order, 0, start_location, start_time, [], 0)

    return best["itinerary"]

def main():
    # Input variables
    start_location = "Alamo Square"
    start_time_hm = "9:00"

    travel_times = {
        ("Alamo Square", "Richmond District"): 12,
        ("Richmond District", "Alamo Square"): 13,
    }

    friends = [
        Friend(name="Timothy", location="Richmond District", window_start_hm="20:45", window_end_hm="21:30", min_duration_min=45)
    ]

    itinerary = compute_best_schedule(start_location, start_time_hm, travel_times, friends)

    output = {"itinerary": itinerary}
    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()