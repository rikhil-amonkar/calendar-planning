import itertools, json

def minutes(h, m):
    return h * 60 + m

def fmt_time(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# Travel times in minutes (directed)
TT = {
    "Haight-Ashbury": {
        "Mission District": 11,
        "Bayview": 18,
        "Pacific Heights": 12,
        "Russian Hill": 17,
        "Fisherman's Wharf": 23,
    },
    "Mission District": {
        "Haight-Ashbury": 12,
        "Bayview": 15,
        "Pacific Heights": 16,
        "Russian Hill": 15,
        "Fisherman's Wharf": 22,
    },
    "Bayview": {
        "Haight-Ashbury": 19,
        "Mission District": 13,
        "Pacific Heights": 23,
        "Russian Hill": 23,
        "Fisherman's Wharf": 25,
    },
    "Pacific Heights": {
        "Haight-Ashbury": 11,
        "Mission District": 15,
        "Bayview": 22,
        "Russian Hill": 7,
        "Fisherman's Wharf": 13,
    },
    "Russian Hill": {
        "Haight-Ashbury": 17,
        "Mission District": 16,
        "Bayview": 23,
        "Pacific Heights": 7,
        "Fisherman's Wharf": 7,
    },
    "Fisherman's Wharf": {
        "Haight-Ashbury": 22,
        "Mission District": 22,
        "Bayview": 26,
        "Pacific Heights": 12,
        "Russian Hill": 7,
    },
}

# Start info
start_location = "Haight-Ashbury"
start_time = minutes(9, 0)

# People constraints
people = [
    {
        "name": "Stephanie",
        "location": "Mission District",
        "window_start": minutes(8, 15),
        "window_end": minutes(13, 45),
        "min_duration": 90,
    },
    {
        "name": "Sandra",
        "location": "Bayview",
        "window_start": minutes(13, 0),
        "window_end": minutes(19, 30),
        "min_duration": 15,
    },
    {
        "name": "Richard",
        "location": "Pacific Heights",
        "window_start": minutes(7, 15),
        "window_end": minutes(10, 15),
        "min_duration": 75,
    },
    {
        "name": "Brian",
        "location": "Russian Hill",
        "window_start": minutes(12, 15),
        "window_end": minutes(16, 0),
        "min_duration": 120,
    },
    {
        "name": "Jason",
        "location": "Fisherman's Wharf",
        "window_start": minutes(8, 30),
        "window_end": minutes(17, 45),
        "min_duration": 60,
    },
]

# Helper to attempt scheduling a sequence (skipping infeasible ones)
def schedule_for_order(order):
    curr_loc = start_location
    curr_time = start_time
    itinerary = []
    total_travel = 0

    for person in order:
        to_loc = person["location"]
        if curr_loc == to_loc:
            travel = 0
        else:
            travel = TT[curr_loc][to_loc]
        arrival = curr_time + travel
        meet_start = max(arrival, person["window_start"])
        meet_end = meet_start + person["min_duration"]
        if meet_end <= person["window_end"]:
            # Feasible meeting; commit travel and meeting
            curr_loc = to_loc
            curr_time = meet_end
            total_travel += travel
            itinerary.append({
                "action": "meet",
                "location": to_loc,
                "person": person["name"],
                "start_time": fmt_time(meet_start),
                "end_time": fmt_time(meet_end),
            })
        else:
            # Skip this person (do not commit travel)
            continue

    return {
        "itinerary": itinerary,
        "count": len(itinerary),
        "end_time": curr_time,
        "total_travel": total_travel,
    }

# Search over all permutations to find the optimal schedule
best = None

for order in itertools.permutations(people):
    result = schedule_for_order(order)
    if best is None:
        best = result
    else:
        # Primary: maximize number of meetings
        if result["count"] > best["count"]:
            best = result
        elif result["count"] == best["count"]:
            # Secondary: earliest finish time
            if result["end_time"] < best["end_time"]:
                best = result
            elif result["end_time"] == best["end_time"]:
                # Tertiary: minimal total travel time
                if result["total_travel"] < best["total_travel"]:
                    best = result

# Output only the itinerary in requested JSON format
output = {"itinerary": best["itinerary"] if best else []}
print(json.dumps(output))