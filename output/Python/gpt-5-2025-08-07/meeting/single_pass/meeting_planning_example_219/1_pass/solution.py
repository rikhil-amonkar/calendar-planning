import json
import itertools

def to_minutes(h, m):
    return h * 60 + m

def fmt_time(mins):
    h = mins // 60
    m = mins % 60
    return f"{h}:{m:02d}"

def build_travel():
    # Travel times in minutes (directed, as provided)
    locations = ["The Castro", "Alamo Square", "Union Square", "Chinatown"]
    travel = {a: {b: None for b in locations} for a in locations}
    # Self travel
    for loc in locations:
        travel[loc][loc] = 0

    # Given travel times
    travel["The Castro"]["Alamo Square"] = 8
    travel["The Castro"]["Union Square"] = 19
    travel["The Castro"]["Chinatown"] = 20

    travel["Alamo Square"]["The Castro"] = 8
    travel["Alamo Square"]["Union Square"] = 14
    travel["Alamo Square"]["Chinatown"] = 16

    travel["Union Square"]["The Castro"] = 19
    travel["Union Square"]["Alamo Square"] = 15
    travel["Union Square"]["Chinatown"] = 7

    travel["Chinatown"]["The Castro"] = 22
    travel["Chinatown"]["Alamo Square"] = 17
    travel["Chinatown"]["Union Square"] = 7

    return travel

def evaluate_order(order, start_loc, start_time, travel):
    n = len(order)
    # Earliest schedule computation (feasibility check)
    earliest_start = [0] * n
    earliest_end = [0] * n
    arrivals = [0] * n

    cur_loc = start_loc
    cur_time = start_time

    for i, p in enumerate(order):
        t_travel = travel[cur_loc][p["location"]]
        if t_travel is None:
            return None  # unreachable
        arrive = cur_time + t_travel
        arrivals[i] = arrive
        start_i = max(arrive, p["start"])
        end_i = start_i + p["min_dur"]
        if end_i > p["end"]:
            return None  # infeasible
        earliest_start[i] = start_i
        earliest_end[i] = end_i
        cur_loc = p["location"]
        cur_time = end_i

    # Backward pass to compute latest feasible ends/starts allowing maximum extension
    latest_end = [0] * n
    latest_start = [0] * n
    for i in range(n - 1, -1, -1):
        p = order[i]
        if i == n - 1:
            latest_end[i] = p["end"]
            latest_start[i] = latest_end[i] - p["min_dur"]
        else:
            next_p = order[i + 1]
            t_travel = travel[p["location"]][next_p["location"]]
            if t_travel is None:
                return None
            latest_end[i] = min(p["end"], latest_start[i + 1] - t_travel)
            latest_start[i] = latest_end[i] - p["min_dur"]

        # Feasibility guard
        if latest_end[i] < earliest_start[i] + p["min_dur"]:
            return None

    # Build actual extended schedule sequentially (respecting travel with extended previous ends)
    itinerary = []
    cur_loc = start_loc
    cur_time = start_time
    total_meet_minutes = 0
    total_travel = 0

    for i, p in enumerate(order):
        t_travel = travel[cur_loc][p["location"]]
        total_travel += t_travel
        arrive = cur_time + t_travel
        start_i = max(arrive, p["start"])
        end_i = latest_end[i]
        # Ensure end_i is not before start_i + min_dur (shouldn't happen due to guards)
        if end_i < start_i + p["min_dur"]:
            return None
        itinerary.append({
            "action": "meet",
            "location": p["location"],
            "person": p["name"],
            "start_time": fmt_time(start_i),
            "end_time": fmt_time(end_i),
        })
        total_meet_minutes += end_i - start_i
        cur_loc = p["location"]
        cur_time = end_i

    return {
        "itinerary": itinerary,
        "count": len(order),
        "total_meet_minutes": total_meet_minutes,
        "total_travel": total_travel
    }

def main():
    # Inputs
    start_location = "The Castro"
    start_time = to_minutes(9, 0)

    # People constraints
    people = [
        {
            "name": "Emily",
            "location": "Alamo Square",
            "start": to_minutes(11, 45),
            "end": to_minutes(15, 15),
            "min_dur": 105
        },
        {
            "name": "Barbara",
            "location": "Union Square",
            "start": to_minutes(16, 45),
            "end": to_minutes(18, 15),
            "min_dur": 60
        },
        {
            "name": "William",
            "location": "Chinatown",
            "start": to_minutes(17, 15),
            "end": to_minutes(19, 0),
            "min_dur": 105
        }
    ]

    travel = build_travel()

    best = None

    # Explore all subsets and permutations
    # Primary objective: maximize number of friends met
    # Secondary: maximize total meeting minutes
    # Tertiary: minimize total travel time
    for r in range(len(people), 0, -1):
        for subset in itertools.combinations(people, r):
            for order in itertools.permutations(subset):
                eval_res = evaluate_order(order, start_location, start_time, travel)
                if not eval_res:
                    continue
                if best is None:
                    best = eval_res
                else:
                    if eval_res["count"] > best["count"]:
                        best = eval_res
                    elif eval_res["count"] == best["count"]:
                        if eval_res["total_meet_minutes"] > best["total_meet_minutes"]:
                            best = eval_res
                        elif eval_res["total_meet_minutes"] == best["total_meet_minutes"]:
                            if eval_res["total_travel"] < best["total_travel"]:
                                best = eval_res
        if best and best["count"] == r:
            # We've found the best for this maximum r; continue to check all for tie-breaks within r handled above
            pass

    if best is None:
        output = {"itinerary": []}
    else:
        output = {"itinerary": best["itinerary"]}

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()