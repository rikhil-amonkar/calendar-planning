import itertools
import json

def time_to_minutes(t):
    # t format "H:MM" in 24-hour time without leading zero for hour
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

def build_travel():
    return {
        "Haight-Ashbury": {
            "Fisherman's Wharf": 23,
            "Richmond District": 10,
            "Mission District": 11,
            "Bayview": 18,
        },
        "Fisherman's Wharf": {
            "Haight-Ashbury": 22,
            "Richmond District": 18,
            "Mission District": 22,
            "Bayview": 26,
        },
        "Richmond District": {
            "Haight-Ashbury": 10,
            "Fisherman's Wharf": 18,
            "Mission District": 20,
            "Bayview": 26,
        },
        "Mission District": {
            "Haight-Ashbury": 12,
            "Fisherman's Wharf": 22,
            "Richmond District": 20,
            "Bayview": 15,
        },
        "Bayview": {
            "Haight-Ashbury": 19,
            "Fisherman's Wharf": 25,
            "Richmond District": 25,
            "Mission District": 13,
        },
    }

def main():
    # Input variables
    start_location = "Haight-Ashbury"
    start_time_str = "9:00"
    start_time = time_to_minutes(start_time_str)

    travel = build_travel()

    people = {
        "Sarah": {
            "location": "Fisherman's Wharf",
            "window_start": time_to_minutes("14:45"),
            "window_end": time_to_minutes("17:30"),
            "min_duration": 105,
        },
        "Mary": {
            "location": "Richmond District",
            "window_start": time_to_minutes("13:00"),
            "window_end": time_to_minutes("19:15"),
            "min_duration": 75,
        },
        "Helen": {
            "location": "Mission District",
            "window_start": time_to_minutes("21:45"),
            "window_end": time_to_minutes("22:30"),
            "min_duration": 30,
        },
        "Thomas": {
            "location": "Bayview",
            "window_start": time_to_minutes("15:15"),
            "window_end": time_to_minutes("18:45"),
            "min_duration": 120,
        },
    }

    def evaluate_order(order):
        current_loc = start_location
        current_time = start_time
        itinerary = []
        total_travel = 0
        total_wait = 0

        for person in order:
            info = people[person]
            dest = info["location"]
            travel_time = travel[current_loc][dest]
            arrival = current_time + travel_time
            start = max(arrival, info["window_start"])
            end = start + info["min_duration"]

            if end > info["window_end"]:
                return None  # infeasible

            wait = max(0, start - arrival)
            total_wait += wait
            total_travel += travel_time

            itinerary.append({
                "action": "meet",
                "location": dest,
                "person": person,
                "start_time": minutes_to_time(start),
                "end_time": minutes_to_time(end),
            })

            current_loc = dest
            current_time = end

        # Return metrics for tie-breaking
        return {
            "itinerary": itinerary,
            "friends_met": len(order),
            "total_wait": total_wait,
            "total_travel": total_travel,
            "finish_time": current_time,
            "order_key": tuple(order),
        }

    best = None

    names = list(people.keys())
    # Search all subsets and permutations, maximizing number of friends met
    for r in range(len(names), 0, -1):
        found_any = False
        for subset in itertools.combinations(names, r):
            for perm in itertools.permutations(subset):
                result = evaluate_order(perm)
                if result is None:
                    continue
                found_any = True
                if best is None:
                    best = result
                else:
                    # Compare with tie-breakers:
                    # 1) maximize friends_met
                    if result["friends_met"] > best["friends_met"]:
                        best = result
                    elif result["friends_met"] == best["friends_met"]:
                        # 2) minimize total_wait
                        if result["total_wait"] < best["total_wait"]:
                            best = result
                        elif result["total_wait"] == best["total_wait"]:
                            # 3) minimize total_travel
                            if result["total_travel"] < best["total_travel"]:
                                best = result
                            elif result["total_travel"] == best["total_travel"]:
                                # 4) earliest finish_time
                                if result["finish_time"] < best["finish_time"]:
                                    best = result
                                elif result["finish_time"] == best["finish_time"]:
                                    # 5) deterministic tie-breaker by lexicographic order of names
                                    if result["order_key"] < best["order_key"]:
                                        best = result
        if found_any:
            break  # no need to consider smaller subsets

    output = {"itinerary": best["itinerary"] if best else []}
    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()