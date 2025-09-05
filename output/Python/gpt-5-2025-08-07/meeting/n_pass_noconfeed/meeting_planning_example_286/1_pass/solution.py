# SOLUTION:
import json
import itertools

def to_minutes(h, m):
    return h * 60 + m

def parse_time(timestr):
    # timestr like "11:30" or "20:15"
    h, m = map(int, timestr.split(":"))
    return to_minutes(h, m)

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def build_travel_times():
    # Travel times in minutes between locations
    return {
        "Union Square": {
            "Union Square": 0,
            "Mission District": 14,
            "Bayview": 15,
            "Sunset District": 26,
        },
        "Mission District": {
            "Union Square": 15,
            "Mission District": 0,
            "Bayview": 15,
            "Sunset District": 24,
        },
        "Bayview": {
            "Union Square": 17,
            "Mission District": 13,
            "Bayview": 0,
            "Sunset District": 23,
        },
        "Sunset District": {
            "Union Square": 30,
            "Mission District": 24,
            "Bayview": 22,
            "Sunset District": 0,
        },
    }

def compute_schedule(start_location, start_time, friends, travel_times):
    # Try all subsets in descending size, and within each, all permutations
    best = None  # (num_meetings, -waiting_time, -spare_time, itinerary)
    n = len(friends)
    friend_keys = list(friends.keys())

    for size in range(n, 0, -1):
        feasible_found = False
        for subset in itertools.combinations(friend_keys, size):
            for order in itertools.permutations(subset):
                current_loc = start_location
                current_time = start_time
                itinerary = []
                total_wait = 0

                feasible = True
                for person in order:
                    info = friends[person]
                    loc = info["location"]
                    travel = travel_times[current_loc][loc]
                    arrival = current_time + travel
                    window_start = info["available_start"]
                    window_end = info["available_end"]
                    duration = info["min_duration"]

                    start_meet = max(arrival, window_start)
                    end_meet = start_meet + duration

                    if end_meet <= window_end:
                        wait = max(0, start_meet - arrival)
                        total_wait += wait
                        itinerary.append({
                            "action": "meet",
                            "location": loc,
                            "person": person,
                            "start_time": fmt_time(start_meet),
                            "end_time": fmt_time(end_meet),
                        })
                        current_loc = loc
                        current_time = end_meet
                    else:
                        feasible = False
                        break

                if feasible:
                    feasible_found = True
                    # Tie-breakers: max meetings, then minimize waiting time, then earliest finishing time
                    finish_time = current_time
                    key = (len(itinerary), -total_wait, -finish_time)
                    if best is None or key > best[0]:
                        best = (key, itinerary)
        if feasible_found:
            break

    return best[1] if best else []

def main():
    # Input variables (constraints)
    travel_times = build_travel_times()

    start_location = "Union Square"
    start_time = parse_time("9:00")

    friends = {
        "Rebecca": {
            "location": "Mission District",
            "available_start": parse_time("11:30"),
            "available_end": parse_time("20:15"),
            "min_duration": 120,
        },
        "Karen": {
            "location": "Bayview",
            "available_start": parse_time("12:45"),
            "available_end": parse_time("15:00"),
            "min_duration": 120,
        },
        "Carol": {
            "location": "Sunset District",
            "available_start": parse_time("10:15"),
            "available_end": parse_time("11:45"),
            "min_duration": 30,
        },
    }

    itinerary = compute_schedule(start_location, start_time, friends, travel_times)

    output = {
        "itinerary": itinerary
    }
    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()