"SOLUTION:"
import itertools
import json

def to_minutes(h, m):
    return h * 60 + m

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def compute_schedule(order, start_loc, start_time, travel, people_by_name):
    time = start_time
    loc = start_loc
    itinerary = []
    total_travel = 0
    total_wait = 0

    for name in order:
        p = people_by_name[name]
        travel_time = travel[loc][p["location"]]
        total_travel += travel_time
        arrival = time + travel_time
        start = max(arrival, p["start"])
        end = start + p["duration"]
        if end > p["end"]:
            return None  # infeasible
        total_wait += max(0, start - arrival)
        itinerary.append({
            "action": "meet",
            "location": p["location"],
            "person": p["name"],
            "start": start,
            "end": end
        })
        time = end
        loc = p["location"]

    return {
        "itinerary": itinerary,
        "end_time": time,
        "total_travel": total_travel,
        "total_wait": total_wait,
        "met_count": len(itinerary)
    }

def main():
    # Input parameters
    start_location = "Bayview"
    start_time = to_minutes(9, 0)  # 9:00

    # Travel times (minutes), directed
    travel = {
        "Bayview": {
            "North Beach": 21,
            "Presidio": 31,
            "Haight-Ashbury": 19,
            "Union Square": 17
        },
        "North Beach": {
            "Bayview": 22,
            "Presidio": 17,
            "Haight-Ashbury": 18,
            "Union Square": 7
        },
        "Presidio": {
            "Bayview": 31,
            "North Beach": 18,
            "Haight-Ashbury": 15,
            "Union Square": 22
        },
        "Haight-Ashbury": {
            "Bayview": 18,
            "North Beach": 19,
            "Presidio": 15,
            "Union Square": 17
        },
        "Union Square": {
            "Bayview": 15,
            "North Beach": 10,
            "Presidio": 24,
            "Haight-Ashbury": 18
        }
    }

    # People constraints
    people = [
        {
            "name": "Barbara",
            "location": "North Beach",
            "start": to_minutes(13, 45),
            "end": to_minutes(20, 15),
            "duration": 60
        },
        {
            "name": "Margaret",
            "location": "Presidio",
            "start": to_minutes(10, 15),
            "end": to_minutes(15, 15),
            "duration": 30
        },
        {
            "name": "Kevin",
            "location": "Haight-Ashbury",
            "start": to_minutes(20, 0),
            "end": to_minutes(20, 45),
            "duration": 30
        },
        {
            "name": "Kimberly",
            "location": "Union Square",
            "start": to_minutes(7, 45),
            "end": to_minutes(16, 45),
            "duration": 30
        }
    ]
    people_by_name = {p["name"]: p for p in people}
    names = [p["name"] for p in people]

    best = None

    # Consider all subsets and permutations
    for k in range(1, len(names) + 1):
        for order in itertools.permutations(names, k):
            result = compute_schedule(order, start_location, start_time, travel, people_by_name)
            if result is None:
                continue
            # Choose best: max people met, then earliest end time, then minimal travel, then minimal waiting
            if best is None:
                best = (order, result)
            else:
                _, bres = best
                if (
                    (result["met_count"] > bres["met_count"]) or
                    (result["met_count"] == bres["met_count"] and result["end_time"] < bres["end_time"]) or
                    (result["met_count"] == bres["met_count"] and result["end_time"] == bres["end_time"] and result["total_travel"] < bres["total_travel"]) or
                    (result["met_count"] == bres["met_count"] and result["end_time"] == bres["end_time"] and result["total_travel"] == bres["total_travel"] and result["total_wait"] < bres["total_wait"])
                ):
                    best = (order, result)

    # Build output JSON
    if best is None:
        output = {"itinerary": []}
    else:
        _, bres = best
        itinerary_out = []
        for item in bres["itinerary"]:
            itinerary_out.append({
                "action": item["action"],
                "location": item["location"],
                "person": item["person"],
                "start_time": fmt_time(item["start"]),
                "end_time": fmt_time(item["end"])
            })
        output = {"itinerary": itinerary_out}

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()