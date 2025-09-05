# SOLUTION:
import json
import itertools

def minutes(h, m):
    return h * 60 + m

def fmt_time(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

def compute_schedule():
    # Input variables
    start_location = "Sunset District"
    start_time = minutes(9, 0)

    travel = {
        "Sunset District": {"North Beach": 29, "Union Square": 30, "Alamo Square": 17},
        "North Beach": {"Sunset District": 27, "Union Square": 7, "Alamo Square": 16},
        "Union Square": {"Sunset District": 26, "North Beach": 10, "Alamo Square": 15},
        "Alamo Square": {"Sunset District": 16, "North Beach": 15, "Union Square": 14},
    }

    friends = {
        "Sarah": {
            "location": "North Beach",
            "start": minutes(16, 0),
            "end": minutes(18, 15),
            "min_duration": 60,
        },
        "Jeffrey": {
            "location": "Union Square",
            "start": minutes(15, 0),
            "end": minutes(22, 0),
            "min_duration": 75,
        },
        "Brian": {
            "location": "Alamo Square",
            "start": minutes(16, 0),
            "end": minutes(17, 30),
            "min_duration": 75,
        },
    }

    names = list(friends.keys())

    def try_order(order):
        current_loc = start_location
        current_time = start_time
        itinerary = []
        total_travel = 0
        total_meeting_time = 0

        for name in order:
            f = friends[name]
            ttime = travel[current_loc][f["location"]]
            total_travel += ttime
            arrival = current_time + ttime
            start = max(arrival, f["start"])
            end = start + f["min_duration"]
            if end > f["end"]:
                return None
            itinerary.append({
                "action": "meet",
                "location": f["location"],
                "person": name,
                "start_time": fmt_time(start),
                "end_time": fmt_time(end),
            })
            total_meeting_time += f["min_duration"]
            current_loc = f["location"]
            current_time = end

        return {
            "itinerary": itinerary,
            "count": len(order),
            "total_travel": total_travel,
            "finish_time": current_time,
            "total_meeting_time": total_meeting_time,
            "order": order,
        }

    best = None

    # Search schedules by maximizing number of friends met; tie-breakers applied as described
    for r in range(len(names), 0, -1):
        feasible = []
        for subset in itertools.combinations(names, r):
            for order in itertools.permutations(subset):
                res = try_order(order)
                if res:
                    feasible.append(res)
        if feasible:
            # Tie-breakers: maximize count (already same), then total_meeting_time desc,
            # then minimize total_travel, then earliest finish_time, then lexicographic order
            feasible.sort(key=lambda x: (-x["total_meeting_time"], x["total_travel"], x["finish_time"], x["order"]))
            best = feasible[0]
            break

    return {"itinerary": best["itinerary"] if best else []}

if __name__ == "__main__":
    result = compute_schedule()
    print(json.dumps(result, ensure_ascii=False))