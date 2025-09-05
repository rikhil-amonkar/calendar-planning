import itertools
import json

def parse_time(t):
    t = t.strip().upper()
    if t.endswith("AM") or t.endswith("PM"):
        ampm = t[-2:]
        hhmm = t[:-2]
        h, m = hhmm.split(":")
        h = int(h)
        m = int(m)
        if ampm == "AM":
            if h == 12:
                h = 0
        else:  # PM
            if h != 12:
                h += 12
        return h * 60 + m
    else:
        # Assume 24-hour "H:MM"
        h, m = t.split(":")
        return int(h) * 60 + int(m)

def minutes_to_str(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def simulate(order, start_loc, start_time, travel):
    current_loc = start_loc
    current_time = start_time
    itinerary = []
    total_travel = 0
    total_wait = 0
    total_meet = 0

    for person in order:
        loc = person["location"]
        # Travel time between current_loc and next location
        if current_loc not in travel or loc not in travel[current_loc]:
            return False, [], 0, 0, 0, 0  # missing travel path
        ttime = travel[current_loc][loc]
        total_travel += ttime
        arrival = current_time + ttime

        # Wait until person's window opens if needed
        meet_start = max(arrival, person["start"])
        wait_here = max(0, person["start"] - arrival)
        total_wait += wait_here

        meet_end = meet_start + person["min_duration"]

        # Check feasibility within window
        if meet_end > person["end"]:
            return False, [], 0, 0, 0, 0

        itinerary.append({
            "action": "meet",
            "location": loc,
            "person": person["name"],
            "start_time": minutes_to_str(meet_start),
            "end_time": minutes_to_str(meet_end),
        })
        total_meet += person["min_duration"]
        current_time = meet_end
        current_loc = loc

    finish_time = current_time
    return True, itinerary, total_meet, total_travel, total_wait, finish_time

def main():
    # Input variables
    start_location = "Fisherman's Wharf"
    arrival_time_str = "9:00AM"

    travel_times = {
        "Fisherman's Wharf": {
            "Presidio": 17,
            "Richmond District": 18,
            "Financial District": 11
        },
        "Presidio": {
            "Fisherman's Wharf": 19,
            "Richmond District": 7,
            "Financial District": 23
        },
        "Richmond District": {
            "Fisherman's Wharf": 18,
            "Presidio": 7,
            "Financial District": 22
        },
        "Financial District": {
            "Fisherman's Wharf": 10,
            "Presidio": 22,
            "Richmond District": 21
        }
    }

    people = [
        {
            "name": "Emily",
            "location": "Presidio",
            "start": parse_time("4:15PM"),
            "end": parse_time("9:00PM"),
            "min_duration": 105
        },
        {
            "name": "Joseph",
            "location": "Richmond District",
            "start": parse_time("5:15PM"),
            "end": parse_time("10:00PM"),
            "min_duration": 120
        },
        {
            "name": "Melissa",
            "location": "Financial District",
            "start": parse_time("3:45PM"),
            "end": parse_time("9:45PM"),
            "min_duration": 75
        }
    ]

    start_time = parse_time(arrival_time_str)

    best = None  # to store (score_tuple, itinerary)
    # Score is a tuple: (num_met, -finish_time, -total_wait, -total_travel)
    # We maximize this tuple
    n = len(people)
    for k in range(n, 0, -1):
        local_best = None
        for combo in itertools.combinations(people, k):
            for order in itertools.permutations(combo):
                feasible, itinerary, total_meet, total_travel, total_wait, finish_time = simulate(
                    order, start_location, start_time, travel_times
                )
                if not feasible:
                    continue
                score = (k, -finish_time, -total_wait, -total_travel)
                if local_best is None or score > local_best[0]:
                    local_best = (score, itinerary)
        if local_best is not None:
            best = local_best
            break

    output = {"itinerary": best[1] if best else []}
    print(json.dumps(output))

if __name__ == "__main__":
    main()