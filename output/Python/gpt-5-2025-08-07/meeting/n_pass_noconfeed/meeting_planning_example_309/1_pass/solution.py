"SOLUTION:"
import json
import itertools

# Input variables: locations, travel times (in minutes), and meeting constraints
locations = [
    "Financial District",
    "Chinatown",
    "Alamo Square",
    "Bayview",
    "Fisherman's Wharf"
]

travel_times = {
    ("Financial District", "Chinatown"): 5,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Bayview"): 19,
    ("Financial District", "Fisherman's Wharf"): 10,

    ("Chinatown", "Financial District"): 5,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Bayview"): 22,
    ("Chinatown", "Fisherman's Wharf"): 8,

    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Chinatown"): 16,
    ("Alamo Square", "Bayview"): 16,
    ("Alamo Square", "Fisherman's Wharf"): 19,

    ("Bayview", "Financial District"): 19,
    ("Bayview", "Chinatown"): 18,
    ("Bayview", "Alamo Square"): 16,
    ("Bayview", "Fisherman's Wharf"): 25,

    ("Fisherman's Wharf", "Financial District"): 11,
    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Alamo Square"): 20,
    ("Fisherman's Wharf", "Bayview"): 26,
}

people = [
    {
        "name": "Nancy",
        "location": "Chinatown",
        "start": 9 * 60 + 30,
        "end": 13 * 60 + 30,
        "min_duration": 90
    },
    {
        "name": "Mary",
        "location": "Alamo Square",
        "start": 7 * 60,
        "end": 21 * 60,
        "min_duration": 75
    },
    {
        "name": "Jessica",
        "location": "Bayview",
        "start": 11 * 60 + 15,
        "end": 13 * 60 + 45,
        "min_duration": 45
    },
    {
        "name": "Rebecca",
        "location": "Fisherman's Wharf",
        "start": 7 * 60,
        "end": 8 * 60 + 30,
        "min_duration": 45
    },
]

start_location = "Financial District"
start_time = 9 * 60  # 9:00


def minutes_to_str(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"


def get_travel_time(origin, dest):
    if origin == dest:
        return 0
    return travel_times[(origin, dest)]


def build_schedule(order):
    itinerary = []
    cur_loc = start_location
    cur_time = start_time
    total_travel = 0
    total_wait = 0

    for p in order:
        travel = get_travel_time(cur_loc, p["location"])
        total_travel += travel
        arrival = cur_time + travel
        start = max(arrival, p["start"])
        wait = max(0, start - arrival)
        total_wait += wait
        end = start + p["min_duration"]

        if end > p["end"]:
            return None  # infeasible

        itinerary.append({
            "action": "meet",
            "location": p["location"],
            "person": p["name"],
            "start_time": minutes_to_str(start),
            "end_time": minutes_to_str(end),
            "_start_min": start,
            "_end_min": end
        })
        cur_loc = p["location"]
        cur_time = end

    finish_time = cur_time
    return {
        "itinerary": itinerary,
        "finish_time": finish_time,
        "total_travel": total_travel,
        "total_wait": total_wait,
        "order_names": tuple(p["name"] for p in order)
    }


def optimize_schedule():
    best = None
    # Primary objective: maximize number of friends met
    # Tie-breakers: earliest finish time, then minimal total travel time, then minimal total wait, then lexicographic by order of names
    n = len(people)
    for k in range(n, 0, -1):
        candidates = []
        for subset in itertools.combinations(people, k):
            for perm in itertools.permutations(subset):
                sched = build_schedule(perm)
                if sched is not None:
                    candidates.append(sched)
        if candidates:
            # Select best according to tie-breakers
            candidates.sort(key=lambda s: (s["finish_time"], s["total_travel"], s["total_wait"], s["order_names"]))
            best = candidates[0]
            break

    if best is None:
        return {"itinerary": []}

    # Clean itinerary for output (remove helper fields)
    clean_itin = []
    for item in best["itinerary"]:
        clean_itin.append({
            "action": item["action"],
            "location": item["location"],
            "person": item["person"],
            "start_time": item["start_time"],
            "end_time": item["end_time"]
        })
    return {"itinerary": clean_itin}


if __name__ == "__main__":
    result = optimize_schedule()
    print(json.dumps(result, indent=2))