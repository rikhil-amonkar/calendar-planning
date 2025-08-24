import itertools
import json

def minutes(h, m):
    return h * 60 + m

def parse_time_24(s):
    # s format: 'H:MM'
    h, m = s.split(':')
    return int(h) * 60 + int(m)

def minutes_to_str(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

def compute_schedule(order, friends_dict, travel, start_loc, start_time):
    current_loc = start_loc
    current_time = start_time
    itinerary = []
    travel_used = 0
    last_loc = start_loc
    last_time = start_time

    for name in order:
        friend = friends_dict[name]
        loc = friend["location"]
        # If travel time missing, skip this friend
        if current_loc not in travel or loc not in travel[current_loc]:
            continue
        arrival = current_time + travel[current_loc][loc]
        start = max(arrival, friend["start"])
        end = start + friend["min_dur"]
        if end <= friend["end"]:
            # Meeting is feasible
            # Accumulate travel used for this successful move
            travel_used += travel[current_loc][loc]
            itinerary.append({
                "action": "meet",
                "location": loc,
                "person": name,
                "start_time": start,
                "end_time": end
            })
            current_loc = loc
            current_time = end
        else:
            # Skip this friend
            continue

    # Compute total travel used from start to first meeting and between meetings
    # We already accumulated it during scheduling (only for successful moves)
    return itinerary, travel_used

def evaluate_itinerary(itinerary, start_loc, start_time, travel):
    count = len(itinerary)
    total_meet_minutes = sum(item["end_time"] - item["start_time"] for item in itinerary)
    # Compute total travel based on actual itinerary
    total_travel = 0
    loc = start_loc
    time = start_time
    for item in itinerary:
        to_loc = item["location"]
        if loc in travel and to_loc in travel[loc]:
            total_travel += travel[loc][to_loc]
        else:
            # If missing a travel entry, penalize heavily (shouldn't happen given inputs)
            total_travel += 10**6
        loc = to_loc
        time = item["end_time"]
    finish_time = time if itinerary else start_time
    return count, total_meet_minutes, total_travel, finish_time

def main():
    # Travel times (in minutes), directional
    travel = {
        "Bayview": {
            "Nob Hill": 20, "Union Square": 17, "Chinatown": 18, "The Castro": 20,
            "Presidio": 31, "Pacific Heights": 23, "Russian Hill": 23
        },
        "Nob Hill": {
            "Bayview": 19, "Union Square": 7, "Chinatown": 6, "The Castro": 17,
            "Presidio": 17, "Pacific Heights": 8, "Russian Hill": 5
        },
        "Union Square": {
            "Bayview": 15, "Nob Hill": 9, "Chinatown": 7, "The Castro": 19,
            "Presidio": 24, "Pacific Heights": 15, "Russian Hill": 13
        },
        "Chinatown": {
            "Bayview": 22, "Nob Hill": 8, "Union Square": 7, "The Castro": 22,
            "Presidio": 19, "Pacific Heights": 10, "Russian Hill": 7
        },
        "The Castro": {
            "Bayview": 19, "Nob Hill": 16, "Union Square": 19, "Chinatown": 20,
            "Presidio": 20, "Pacific Heights": 16, "Russian Hill": 18
        },
        "Presidio": {
            "Bayview": 31, "Nob Hill": 18, "Union Square": 22, "Chinatown": 21,
            "The Castro": 21, "Pacific Heights": 11, "Russian Hill": 14
        },
        "Pacific Heights": {
            "Bayview": 22, "Nob Hill": 8, "Union Square": 12, "Chinatown": 11,
            "The Castro": 16, "Presidio": 11, "Russian Hill": 7
        },
        "Russian Hill": {
            "Bayview": 23, "Nob Hill": 5, "Union Square": 11, "Chinatown": 9,
            "The Castro": 21, "Presidio": 14, "Pacific Heights": 7
        }
    }

    # Meeting constraints
    friends = [
        {"name": "Paul", "location": "Nob Hill", "start": "16:15", "end": "21:15", "min_dur": 60},
        {"name": "Carol", "location": "Union Square", "start": "18:00", "end": "20:15", "min_dur": 120},
        {"name": "Patricia", "location": "Chinatown", "start": "20:00", "end": "21:30", "min_dur": 75},
        {"name": "Karen", "location": "The Castro", "start": "17:00", "end": "19:00", "min_dur": 45},
        {"name": "Nancy", "location": "Presidio", "start": "11:45", "end": "22:00", "min_dur": 30},
        {"name": "Jeffrey", "location": "Pacific Heights", "start": "20:00", "end": "20:45", "min_dur": 45},
        {"name": "Matthew", "location": "Russian Hill", "start": "15:45", "end": "21:45", "min_dur": 75},
    ]

    # Convert times to minutes since midnight (24h)
    for f in friends:
        f["start"] = parse_time_24(f["start"])
        f["end"] = parse_time_24(f["end"])

    friends_dict = {f["name"]: f for f in friends}
    friend_names = [f["name"] for f in friends]

    # Start parameters
    start_location = "Bayview"
    start_time = parse_time_24("9:00")  # Arrive at Bayview at 9:00

    best_itinerary = []
    best_metrics = (-1, -1, float('inf'), float('inf'))  # count, total_meet_minutes, total_travel, finish_time (to be minimized where applicable)

    # Explore all permutations and greedily accept feasible meetings in that order
    for order in itertools.permutations(friend_names):
        itinerary, _ = compute_schedule(order, friends_dict, travel, start_location, start_time)
        count, total_meet_minutes, total_travel, finish_time = evaluate_itinerary(itinerary, start_location, start_time, travel)

        # Optimization criteria: maximize count, then total_meet_minutes; then minimize total_travel; then minimize finish_time
        metrics = (count, total_meet_minutes, -total_travel, -finish_time)  # invert last two for max comparison
        best_metrics_cmp = (best_metrics[0], best_metrics[1], -best_metrics[2], -best_metrics[3])

        if metrics > best_metrics_cmp:
            best_itinerary = itinerary
            best_metrics = (count, total_meet_minutes, total_travel, finish_time)

    # Prepare output JSON with formatted times
    output_itinerary = []
    for item in best_itinerary:
        output_itinerary.append({
            "action": "meet",
            "location": item["location"],
            "person": item["person"],
            "start_time": minutes_to_str(item["start_time"]),
            "end_time": minutes_to_str(item["end_time"])
        })

    result = {"itinerary": output_itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()