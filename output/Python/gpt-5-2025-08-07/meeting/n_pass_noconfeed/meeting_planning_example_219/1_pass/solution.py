# SOLUTION:
import json
import itertools

def to_minutes(t):
    # t format 'H:MM' 24-hour
    h, m = t.split(':')
    return int(h) * 60 + int(m)

def fmt_time(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

def schedule_permutation(order, start_loc, start_time, travel, people_by_name):
    itinerary = []
    total_travel = 0
    cur_loc = start_loc
    cur_time = start_time

    for name in order:
        p = people_by_name[name]
        t_travel = travel[cur_loc][p["location"]]
        total_travel += t_travel
        arrival = cur_time + t_travel
        start_meet = max(arrival, p["start"])
        end_meet = start_meet + p["min_duration"]
        if end_meet > p["end"]:
            return None  # infeasible
        itinerary.append({
            "action": "meet",
            "location": p["location"],
            "person": p["name"],
            "start_time": fmt_time(start_meet),
            "end_time": fmt_time(end_meet),
            "_start": start_meet,
            "_end": end_meet
        })
        cur_loc = p["location"]
        cur_time = end_meet

    # compute total meeting time (currently min durations)
    total_meet_time = sum(item["_end"] - item["_start"] for item in itinerary)
    # strip helper fields
    for item in itinerary:
        item.pop("_start", None)
        item.pop("_end", None)
    return {
        "itinerary": itinerary,
        "num_met": len(order),
        "total_meet_time": total_meet_time,
        "total_travel_time": total_travel
    }

def main():
    # Input variables (constraints and travel times)
    start_location = "The Castro"
    start_time_str = "9:00"

    friends = [
        {"name": "Emily", "location": "Alamo Square", "start_str": "11:45", "end_str": "15:15", "min_duration": 105},
        {"name": "Barbara", "location": "Union Square", "start_str": "16:45", "end_str": "18:15", "min_duration": 60},
        {"name": "William", "location": "Chinatown", "start_str": "17:15", "end_str": "19:00", "min_duration": 105},
    ]

    travel_times = {
        "The Castro": {
            "Alamo Square": 8,
            "Union Square": 19,
            "Chinatown": 20
        },
        "Alamo Square": {
            "The Castro": 8,
            "Union Square": 14,
            "Chinatown": 16
        },
        "Union Square": {
            "The Castro": 19,
            "Alamo Square": 15,
            "Chinatown": 7
        },
        "Chinatown": {
            "The Castro": 22,
            "Alamo Square": 17,
            "Union Square": 7
        }
    }

    # Preprocess times
    start_time = to_minutes(start_time_str)
    for f in friends:
        f["start"] = to_minutes(f["start_str"])
        f["end"] = to_minutes(f["end_str"])

    people_by_name = {f["name"]: f for f in friends}
    names = [f["name"] for f in friends]

    best = None
    # Search subsets and permutations to maximize number met, then total meeting time, then minimize travel time
    for r in range(len(names), 0, -1):
        any_feasible_for_r = False
        for subset in itertools.combinations(names, r):
            for perm in itertools.permutations(subset):
                result = schedule_permutation(perm, start_location, start_time, travel_times, people_by_name)
                if result is None:
                    continue
                any_feasible_for_r = True
                if best is None:
                    best = result
                else:
                    # Compare: more people, then more meeting time, then less travel
                    if (result["num_met"] > best["num_met"] or
                        (result["num_met"] == best["num_met"] and result["total_meet_time"] > best["total_meet_time"]) or
                        (result["num_met"] == best["num_met"] and result["total_meet_time"] == best["total_meet_time"] and result["total_travel_time"] < best["total_travel_time"])):
                        best = result
        if any_feasible_for_r:
            break

    if best is None:
        output = {"itinerary": []}
    else:
        output = {"itinerary": best["itinerary"]}

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()