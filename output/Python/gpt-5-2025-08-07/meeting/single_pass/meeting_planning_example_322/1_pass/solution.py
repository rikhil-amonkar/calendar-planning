import itertools
import json

def minutes(h, m=0):
    return h * 60 + m

def fmt_time(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

def get_travel_time(travel_times, a, b):
    if a == b:
        return 0
    if a in travel_times and b in travel_times[a]:
        return travel_times[a][b]
    if b in travel_times and a in travel_times[b]:
        return travel_times[b][a]
    raise ValueError(f"No travel time between {a} and {b}")

def schedule_for_order(order, travel_times, start_location, start_time):
    current_loc = start_location
    current_time = start_time
    itinerary = []
    total_travel = 0
    total_wait = 0

    for friend in order:
        travel = get_travel_time(travel_times, current_loc, friend["location"])
        arrival = current_time + travel
        start = max(arrival, friend["window_start"])
        end = start + friend["min_duration"]
        if end > friend["window_end"]:
            return None  # infeasible
        itinerary.append({
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": fmt_time(start),
            "end_time": fmt_time(end),
        })
        total_travel += travel
        total_wait += max(0, start - arrival)
        current_loc = friend["location"]
        current_time = end

    return {
        "itinerary": itinerary,
        "end_time": current_time,
        "total_travel": total_travel,
        "total_wait": total_wait,
        "met_count": len(order)
    }

def optimize_schedule(friends, travel_times, start_location, start_time):
    best = None

    # Try all subsets of friends from largest to smallest
    for r in range(len(friends), 0, -1):
        feasible_found = False
        for subset in itertools.combinations(friends, r):
            for order in itertools.permutations(subset):
                res = schedule_for_order(order, travel_times, start_location, start_time)
                if res is None:
                    continue
                feasible_found = True
                if best is None:
                    best = res
                else:
                    # Primary: maximize number of friends met
                    if res["met_count"] > best["met_count"]:
                        best = res
                    elif res["met_count"] == best["met_count"]:
                        # Secondary: minimize end time (finish earlier)
                        if res["end_time"] < best["end_time"]:
                            best = res
                        elif res["end_time"] == best["end_time"]:
                            # Tertiary: minimize total travel
                            if res["total_travel"] < best["total_travel"]:
                                best = res
                            elif res["total_travel"] == best["total_travel"]:
                                # Quaternary: minimize total waiting
                                if res["total_wait"] < best["total_wait"]:
                                    best = res
        if feasible_found:
            break  # no need to check smaller subsets
    return best

def main():
    # Input variables (meeting constraints and travel times)
    start_location = "Sunset District"
    start_time = minutes(9, 0)  # 9:00

    travel_times = {
        "Sunset District": {
            "Russian Hill": 24,
            "Chinatown": 30,
            "Presidio": 16,
            "Fisherman's Wharf": 29
        },
        "Russian Hill": {
            "Sunset District": 23,
            "Chinatown": 9,
            "Presidio": 14,
            "Fisherman's Wharf": 7
        },
        "Chinatown": {
            "Sunset District": 29,
            "Russian Hill": 7,
            "Presidio": 19,
            "Fisherman's Wharf": 8
        },
        "Presidio": {
            "Sunset District": 15,
            "Russian Hill": 14,
            "Chinatown": 21,
            "Fisherman's Wharf": 19
        },
        "Fisherman's Wharf": {
            "Sunset District": 27,
            "Russian Hill": 7,
            "Chinatown": 12,
            "Presidio": 17
        }
    }

    friends = [
        {
            "name": "William",
            "location": "Russian Hill",
            "window_start": minutes(18, 30),
            "window_end": minutes(20, 45),
            "min_duration": 105
        },
        {
            "name": "Michelle",
            "location": "Chinatown",
            "window_start": minutes(8, 15),
            "window_end": minutes(14, 0),
            "min_duration": 15
        },
        {
            "name": "George",
            "location": "Presidio",
            "window_start": minutes(10, 30),
            "window_end": minutes(18, 45),
            "min_duration": 30
        },
        {
            "name": "Robert",
            "location": "Fisherman's Wharf",
            "window_start": minutes(9, 0),
            "window_end": minutes(13, 45),
            "min_duration": 30
        }
    ]

    result = optimize_schedule(friends, travel_times, start_location, start_time)

    # Prepare JSON output
    if result is None:
        output = {"itinerary": []}
    else:
        output = {"itinerary": result["itinerary"]}

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()