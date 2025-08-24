import json
from itertools import combinations, permutations, chain

def h2m(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def m2h(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

def travel_time(a, b, dists):
    if a == b:
        return 0
    return dists[a][b]

def compute_schedule(order, friends, start_loc, start_time_m, dists):
    current_loc = start_loc
    current_time = start_time_m
    total_travel = 0
    itinerary = []

    for name in order:
        p = friends[name]
        loc = p["location"]
        t_travel = travel_time(current_loc, loc, dists)
        arrival = current_time + t_travel
        total_travel += t_travel

        window_start = p["window_start"]
        window_end = p["window_end"]
        min_dur = p["min_duration"]

        start_meet = max(arrival, window_start)
        if start_meet + min_dur > window_end:
            return None  # infeasible

        end_meet = start_meet + min_dur
        itinerary.append({
            "action": "meet",
            "location": loc,
            "person": name,
            "start_time": m2h(start_meet),
            "end_time": m2h(end_meet)
        })

        current_loc = loc
        current_time = end_meet

    return {
        "itinerary": itinerary,
        "finish_time": current_time,
        "total_travel": total_travel,
        "met_count": len(itinerary)
    }

def powerset(iterable):
    s = list(iterable)
    for r in range(1, len(s) + 1):
        for comb in combinations(s, r):
            yield comb

def main():
    # Directed travel times in minutes
    dists = {
        "Bayview": {
            "Embarcadero": 19,
            "Richmond District": 25,
            "Fisherman's Wharf": 25
        },
        "Embarcadero": {
            "Bayview": 21,
            "Richmond District": 21,
            "Fisherman's Wharf": 6
        },
        "Richmond District": {
            "Bayview": 26,
            "Embarcadero": 19,
            "Fisherman's Wharf": 18
        },
        "Fisherman's Wharf": {
            "Bayview": 26,
            "Embarcadero": 8,
            "Richmond District": 18
        }
    }

    # Meeting constraints
    friends = {
        "Jessica": {
            "location": "Embarcadero",
            "window_start": h2m("16:45"),
            "window_end": h2m("19:00"),
            "min_duration": 30
        },
        "Sandra": {
            "location": "Richmond District",
            "window_start": h2m("18:30"),
            "window_end": h2m("21:45"),
            "min_duration": 120
        },
        "Jason": {
            "location": "Fisherman's Wharf",
            "window_start": h2m("16:00"),
            "window_end": h2m("16:45"),
            "min_duration": 30
        }
    }

    start_location = "Bayview"
    start_time = h2m("9:00")

    names = list(friends.keys())

    best = None

    # Explore all subsets and permutations to maximize number of friends met
    for subset in powerset(names):
        for order in permutations(subset):
            candidate = compute_schedule(order, friends, start_location, start_time, dists)
            if candidate is None:
                continue

            if best is None:
                best = candidate
            else:
                # Compare by: 1) more meetings 2) earlier finish time 3) less total travel
                if (candidate["met_count"] > best["met_count"] or
                    (candidate["met_count"] == best["met_count"] and candidate["finish_time"] < best["finish_time"]) or
                    (candidate["met_count"] == best["met_count"] and candidate["finish_time"] == best["finish_time"] and candidate["total_travel"] < best["total_travel"])):
                    best = candidate

    output = {"itinerary": [] if best is None else best["itinerary"]}
    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()