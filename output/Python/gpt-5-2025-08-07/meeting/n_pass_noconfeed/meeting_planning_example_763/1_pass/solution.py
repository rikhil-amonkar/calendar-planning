import itertools
import json

def parse_time(t):
    t = t.strip().upper()
    # Expected formats like '3:15PM' or '9:00AM'
    if t.endswith("AM") or t.endswith("PM"):
        ampm = t[-2:]
        hh_mm = t[:-2]
    else:
        # 24-hour format fallback: '13:30'
        ampm = None
        hh_mm = t
    hh, mm = hh_mm.split(":")
    h = int(hh)
    m = int(mm)
    if ampm == "AM":
        if h == 12:
            h = 0
    elif ampm == "PM":
        if h != 12:
            h += 12
    return h * 60 + m

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Travel time map (directed, in minutes)
travel = {
    "Chinatown": {
        "Embarcadero": 5,
        "Pacific Heights": 10,
        "Russian Hill": 7,
        "Haight-Ashbury": 19,
        "Golden Gate Park": 23,
        "Fisherman's Wharf": 8,
        "Sunset District": 29,
        "The Castro": 22,
    },
    "Embarcadero": {
        "Chinatown": 7,
        "Pacific Heights": 11,
        "Russian Hill": 8,
        "Haight-Ashbury": 21,
        "Golden Gate Park": 25,
        "Fisherman's Wharf": 6,
        "Sunset District": 30,
        "The Castro": 25,
    },
    "Pacific Heights": {
        "Chinatown": 11,
        "Embarcadero": 10,
        "Russian Hill": 7,
        "Haight-Ashbury": 11,
        "Golden Gate Park": 15,
        "Fisherman's Wharf": 13,
        "Sunset District": 21,
        "The Castro": 16,
    },
    "Russian Hill": {
        "Chinatown": 9,
        "Embarcadero": 8,
        "Pacific Heights": 7,
        "Haight-Ashbury": 17,
        "Golden Gate Park": 21,
        "Fisherman's Wharf": 7,
        "Sunset District": 23,
        "The Castro": 21,
    },
    "Haight-Ashbury": {
        "Chinatown": 19,
        "Embarcadero": 20,
        "Pacific Heights": 12,
        "Russian Hill": 17,
        "Golden Gate Park": 7,
        "Fisherman's Wharf": 23,
        "Sunset District": 15,
        "The Castro": 6,
    },
    "Golden Gate Park": {
        "Chinatown": 23,
        "Embarcadero": 25,
        "Pacific Heights": 16,
        "Russian Hill": 19,
        "Haight-Ashbury": 7,
        "Fisherman's Wharf": 24,
        "Sunset District": 10,
        "The Castro": 13,
    },
    "Fisherman's Wharf": {
        "Chinatown": 12,
        "Embarcadero": 8,
        "Pacific Heights": 12,
        "Russian Hill": 7,
        "Haight-Ashbury": 22,
        "Golden Gate Park": 25,
        "Sunset District": 27,
        "The Castro": 27,
    },
    "Sunset District": {
        "Chinatown": 30,
        "Embarcadero": 30,
        "Pacific Heights": 21,
        "Russian Hill": 24,
        "Haight-Ashbury": 15,
        "Golden Gate Park": 11,
        "Fisherman's Wharf": 29,
        "The Castro": 17,
    },
    "The Castro": {
        "Chinatown": 22,
        "Embarcadero": 22,
        "Pacific Heights": 16,
        "Russian Hill": 18,
        "Haight-Ashbury": 6,
        "Golden Gate Park": 11,
        "Fisherman's Wharf": 24,
        "Sunset District": 17,
    },
}

# Meeting constraints
friends_raw = {
    "Richard": {"location": "Embarcadero", "start": "3:15PM", "end": "6:45PM", "min_minutes": 90},
    "Mark": {"location": "Pacific Heights", "start": "3:00PM", "end": "5:00PM", "min_minutes": 45},
    "Matthew": {"location": "Russian Hill", "start": "5:30PM", "end": "9:00PM", "min_minutes": 90},
    "Rebecca": {"location": "Haight-Ashbury", "start": "2:45PM", "end": "6:00PM", "min_minutes": 60},
    "Melissa": {"location": "Golden Gate Park", "start": "1:45PM", "end": "5:30PM", "min_minutes": 90},
    "Margaret": {"location": "Fisherman's Wharf", "start": "2:45PM", "end": "8:15PM", "min_minutes": 15},
    "Emily": {"location": "Sunset District", "start": "3:45PM", "end": "5:00PM", "min_minutes": 45},
    "George": {"location": "The Castro", "start": "2:00PM", "end": "4:15PM", "min_minutes": 75},
}

friends = {}
for name, info in friends_raw.items():
    friends[name] = {
        "location": info["location"],
        "start": parse_time(info["start"]),
        "end": parse_time(info["end"]),
        "min": info["min_minutes"],
    }

start_location = "Chinatown"
start_time = parse_time("9:00AM")

def feasible_schedule_for_order(order):
    """
    Given an order (tuple/list) of friend names, build the earliest-feasible schedule.
    Returns (itinerary_list, total_travel_minutes, finish_time_minutes) or None if infeasible.
    """
    curr_loc = start_location
    curr_time = start_time
    total_travel = 0
    itinerary = []

    for friend in order:
        loc = friends[friend]["location"]
        a_start = friends[friend]["start"]
        a_end = friends[friend]["end"]
        min_dur = friends[friend]["min"]

        # Travel time
        if curr_loc not in travel or loc not in travel[curr_loc]:
            return None
        t_travel = travel[curr_loc][loc]
        total_travel += t_travel
        arrival = curr_time + t_travel

        # Wait if early
        meet_start = max(arrival, a_start)
        meet_end = meet_start + min_dur

        if meet_end > a_end:
            return None

        itinerary.append({
            "action": "meet",
            "location": loc,
            "person": friend,
            "start_time": meet_start,
            "end_time": meet_end,
        })
        curr_loc = loc
        curr_time = meet_end

    return itinerary, total_travel, curr_time

def select_best_itinerary():
    people = list(friends.keys())
    n = len(people)

    best = None
    best_count = 0
    found_this_k = False

    # Maximize number of friends met; check k from n down to 1
    for k in range(n, 0, -1):
        found_this_k = False
        for order in itertools.permutations(people, k):
            res = feasible_schedule_for_order(order)
            if not res:
                continue
            found_this_k = True
            itinerary, total_travel, finish_time = res

            # Comparison: maximize meetings count, then minimize travel, then minimize finish time, then lexicographic determinism
            count = len(itinerary)

            # Prepare comparison tuple
            comp_tuple = (-count, total_travel, finish_time, tuple(entry["person"] for entry in itinerary), tuple(entry["start_time"] for entry in itinerary))
            if best is None or comp_tuple < best["comp"]:
                best = {"itinerary": itinerary, "comp": comp_tuple}
                best_count = count

        if found_this_k:
            # We've evaluated all permutations of size k; that's the maximal count achievable
            break

    if best is None:
        return []

    # Convert minute times to formatted strings
    formatted = []
    for entry in best["itinerary"]:
        formatted.append({
            "action": "meet",
            "location": entry["location"],
            "person": entry["person"],
            "start_time": fmt_time(entry["start_time"]),
            "end_time": fmt_time(entry["end_time"]),
        })
    return formatted

def main():
    itinerary = select_best_itinerary()
    output = {"itinerary": itinerary}
    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()