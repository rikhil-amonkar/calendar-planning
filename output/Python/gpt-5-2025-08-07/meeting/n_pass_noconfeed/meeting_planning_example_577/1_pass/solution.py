import itertools
import json

def to_minutes(time_str):
    # time_str in "H:MM" 24-hour format
    h, m = map(int, time_str.split(":"))
    return h * 60 + m

def fmt_time(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

def compute_schedule(order, start_loc, start_time, people, travel):
    itinerary = []
    current_loc = start_loc
    current_time = start_time
    total_wait = 0

    for name in order:
        p = people[name]
        # travel time from current_loc to person's location
        t = travel.get((current_loc, p["location"]), None)
        if t is None:
            # cannot travel (should not happen if data complete)
            continue
        arrival = current_time + t
        start = max(arrival, p["start"])
        end = start + p["min_duration"]
        if end <= p["end"]:
            wait = max(0, start - arrival)
            total_wait += wait
            itinerary.append({
                "action": "meet",
                "location": p["location"],
                "person": name,
                "start_time": fmt_time(start),
                "end_time": fmt_time(end),
            })
            current_loc = p["location"]
            current_time = end
        else:
            # cannot meet this person in this order; skip
            continue

    finish_time = current_time
    return itinerary, total_wait, finish_time

def main():
    # Travel times (minutes)
    travel = {
        ("Haight-Ashbury", "Russian Hill"): 17,
        ("Haight-Ashbury", "Fisherman's Wharf"): 23,
        ("Haight-Ashbury", "Nob Hill"): 15,
        ("Haight-Ashbury", "Golden Gate Park"): 7,
        ("Haight-Ashbury", "Alamo Square"): 5,
        ("Haight-Ashbury", "Pacific Heights"): 12,

        ("Russian Hill", "Haight-Ashbury"): 17,
        ("Russian Hill", "Fisherman's Wharf"): 7,
        ("Russian Hill", "Nob Hill"): 5,
        ("Russian Hill", "Golden Gate Park"): 21,
        ("Russian Hill", "Alamo Square"): 15,
        ("Russian Hill", "Pacific Heights"): 7,

        ("Fisherman's Wharf", "Haight-Ashbury"): 22,
        ("Fisherman's Wharf", "Russian Hill"): 7,
        ("Fisherman's Wharf", "Nob Hill"): 11,
        ("Fisherman's Wharf", "Golden Gate Park"): 25,
        ("Fisherman's Wharf", "Alamo Square"): 20,
        ("Fisherman's Wharf", "Pacific Heights"): 12,

        ("Nob Hill", "Haight-Ashbury"): 13,
        ("Nob Hill", "Russian Hill"): 5,
        ("Nob Hill", "Fisherman's Wharf"): 11,
        ("Nob Hill", "Golden Gate Park"): 17,
        ("Nob Hill", "Alamo Square"): 11,
        ("Nob Hill", "Pacific Heights"): 8,

        ("Golden Gate Park", "Haight-Ashbury"): 7,
        ("Golden Gate Park", "Russian Hill"): 19,
        ("Golden Gate Park", "Fisherman's Wharf"): 24,
        ("Golden Gate Park", "Nob Hill"): 20,
        ("Golden Gate Park", "Alamo Square"): 10,
        ("Golden Gate Park", "Pacific Heights"): 16,

        ("Alamo Square", "Haight-Ashbury"): 5,
        ("Alamo Square", "Russian Hill"): 13,
        ("Alamo Square", "Fisherman's Wharf"): 19,
        ("Alamo Square", "Nob Hill"): 11,
        ("Alamo Square", "Golden Gate Park"): 9,
        ("Alamo Square", "Pacific Heights"): 10,

        ("Pacific Heights", "Haight-Ashbury"): 11,
        ("Pacific Heights", "Russian Hill"): 7,
        ("Pacific Heights", "Fisherman's Wharf"): 13,
        ("Pacific Heights", "Nob Hill"): 8,
        ("Pacific Heights", "Golden Gate Park"): 15,
        ("Pacific Heights", "Alamo Square"): 10,
    }

    # Constraints
    people = {
        "Stephanie": {
            "location": "Russian Hill",
            "start": to_minutes("20:00"),
            "end": to_minutes("20:45"),
            "min_duration": 15,
        },
        "Kevin": {
            "location": "Fisherman's Wharf",
            "start": to_minutes("19:15"),
            "end": to_minutes("21:45"),
            "min_duration": 75,
        },
        "Robert": {
            "location": "Nob Hill",
            "start": to_minutes("7:45"),
            "end": to_minutes("10:30"),
            "min_duration": 90,
        },
        "Steven": {
            "location": "Golden Gate Park",
            "start": to_minutes("8:30"),
            "end": to_minutes("17:00"),
            "min_duration": 75,
        },
        "Anthony": {
            "location": "Alamo Square",
            "start": to_minutes("7:45"),
            "end": to_minutes("19:45"),
            "min_duration": 15,
        },
        "Sandra": {
            "location": "Pacific Heights",
            "start": to_minutes("14:45"),
            "end": to_minutes("21:45"),
            "min_duration": 45,
        },
    }

    start_loc = "Haight-Ashbury"
    start_time = to_minutes("9:00")

    names = list(people.keys())
    best = {
        "count": -1,
        "wait": float("inf"),
        "finish": float("inf"),
        "itinerary": [],
    }

    # Try all permutations (algorithmically search different schedules)
    for order in itertools.permutations(names):
        itinerary, total_wait, finish_time = compute_schedule(order, start_loc, start_time, people, travel)
        count = len(itinerary)
        # Keep the best according to criteria:
        # 1) maximize number of meetings
        # 2) minimize total waiting time
        # 3) earliest finish time
        if (count > best["count"] or
            (count == best["count"] and (total_wait < best["wait"] or
                                         (total_wait == best["wait"] and finish_time < best["finish"])))):
            best["count"] = count
            best["wait"] = total_wait
            best["finish"] = finish_time
            best["itinerary"] = itinerary

    result = {
        "itinerary": best["itinerary"]
    }

    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    main()