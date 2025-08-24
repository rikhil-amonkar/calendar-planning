import itertools
import json

def parse_12h_to_minutes(s):
    s = s.strip().upper()
    if s.endswith("AM") or s.endswith("PM"):
        ampm = s[-2:]
        time = s[:-2].strip()
    else:
        time = s
        ampm = None
    h, m = map(int, time.split(":"))
    if ampm == "AM":
        if h == 12:
            h = 0
    elif ampm == "PM":
        if h != 12:
            h += 12
    return h * 60 + m

def minutes_to_hhmm(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Input variables (constraints and travel times)
start_location = "Sunset District"
arrival_time = parse_12h_to_minutes("9:00AM")

travel_times = {
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Fisherman's Wharf"): 29,

    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Fisherman's Wharf"): 7,

    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Fisherman's Wharf"): 8,

    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Fisherman's Wharf"): 19,

    ("Fisherman's Wharf", "Sunset District"): 27,
    ("Fisherman's Wharf", "Russian Hill"): 7,
    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Presidio"): 17,
}

friends = [
    {
        "name": "William",
        "location": "Russian Hill",
        "start": parse_12h_to_minutes("6:30PM"),
        "end": parse_12h_to_minutes("8:45PM"),
        "min_duration": 105,
    },
    {
        "name": "Michelle",
        "location": "Chinatown",
        "start": parse_12h_to_minutes("8:15AM"),
        "end": parse_12h_to_minutes("2:00PM"),
        "min_duration": 15,
    },
    {
        "name": "George",
        "location": "Presidio",
        "start": parse_12h_to_minutes("10:30AM"),
        "end": parse_12h_to_minutes("6:45PM"),
        "min_duration": 30,
    },
    {
        "name": "Robert",
        "location": "Fisherman's Wharf",
        "start": parse_12h_to_minutes("9:00AM"),
        "end": parse_12h_to_minutes("1:45PM"),
        "min_duration": 30,
    },
]

def compute_schedule(order):
    curr_loc = start_location
    curr_time = arrival_time
    itinerary = []
    total_travel = 0

    # We will store preliminary meeting slots (start, end) then possibly extend each where useful
    meetings = []

    for idx, fr in enumerate(order):
        tkey = (curr_loc, fr["location"])
        if tkey not in travel_times:
            return None
        travel = travel_times[tkey]
        total_travel += travel
        arrival = curr_time + travel

        # Meeting start cannot be before friend's available start
        start_time_meet = max(arrival, fr["start"])
        end_time_meet = start_time_meet + fr["min_duration"]

        # If we cannot finish the minimum meeting before their end -> infeasible
        if end_time_meet > fr["end"]:
            return None

        meetings.append({
            "person": fr["name"],
            "location": fr["location"],
            "start": start_time_meet,
            "end": end_time_meet,  # may extend later
            "window_end": fr["end"],
        })

        curr_loc = fr["location"]
        curr_time = end_time_meet

    # Now greedily extend meetings to reduce idle time before next and to fill the last meeting to its window end
    for i in range(len(meetings)):
        if i < len(meetings) - 1:
            curr = meetings[i]
            nxt = meetings[i+1]
            # compute travel time from curr to next
            tkey = (curr["location"], nxt["location"])
            if tkey not in travel_times:
                return None
            travel = travel_times[tkey]
            # If leaving at current end causes early arrival to next start, we can extend current meeting
            earliest_arrival_next_if_leave_now = curr["end"] + travel
            idle = nxt["start"] - earliest_arrival_next_if_leave_now
            if idle > 0:
                # extend by at most the idle, but not beyond current friend's window end
                extension = min(idle, curr["window_end"] - curr["end"])
                curr["end"] += extension
                # Also shift start of next meeting if needed (we still recompute start when building final itinerary)
        else:
            # Last meeting: extend to end of window
            meetings[i]["end"] = meetings[i]["window_end"]

    # Reconstruct actual itinerary times considering the extensions we chose and actual travel and earliest starts
    final_itinerary = []
    curr_loc = start_location
    curr_time = arrival_time
    total_travel_confirm = 0
    total_meeting_time = 0

    for i, fr in enumerate(order):
        tkey = (curr_loc, fr["location"])
        travel = travel_times[tkey]
        total_travel_confirm += travel
        arrival = curr_time + travel
        # schedule start as max(arrival, fr["start"])
        start_time_meet = max(arrival, fr["start"])

        # For the end time, use the possibly extended end we computed, but ensure not earlier than start and within window
        planned_end = meetings[i]["end"]
        # ensure not ending before starting, clip if necessary
        if planned_end < start_time_meet:
            return None
        # ensure still within window
        if planned_end > fr["end"]:
            planned_end = fr["end"]
        # ensure minimum duration
        if planned_end - start_time_meet < fr["min_duration"]:
            # Try to push end to at least min duration if possible
            needed = fr["min_duration"] - (planned_end - start_time_meet)
            if planned_end + needed <= fr["end"]:
                planned_end += needed
            else:
                return None

        final_itinerary.append({
            "action": "meet",
            "location": fr["location"],
            "person": fr["name"],
            "start_time": minutes_to_hhmm(start_time_meet),
            "end_time": minutes_to_hhmm(planned_end),
            "_start": start_time_meet,
            "_end": planned_end,
        })
        total_meeting_time += (planned_end - start_time_meet)
        curr_loc = fr["location"]
        curr_time = planned_end

    finish_time = curr_time

    return {
        "itinerary": final_itinerary,
        "total_meeting_time": total_meeting_time,
        "total_travel_time": total_travel_confirm,
        "finish_time": finish_time,
        "count": len(final_itinerary),
    }

# Explore all subsets and permutations to maximize number of friends met, then meeting time, then minimize travel, then earlier finish
best = None
best_key = None

all_friends = friends[:]
n = len(all_friends)

for r in range(n, 0, -1):
    for subset in itertools.combinations(all_friends, r):
        for perm in itertools.permutations(subset):
            result = compute_schedule(list(perm))
            if result is None:
                continue
            key = (-result["count"], -result["total_meeting_time"], result["total_travel_time"], result["finish_time"])
            if best is None or key < best_key:
                best = result
                best_key = key

# Prepare output
output = {"itinerary": []}
if best is not None:
    # Strip helper fields
    for entry in best["itinerary"]:
        output["itinerary"].append({
            "action": entry["action"],
            "location": entry["location"],
            "person": entry["person"],
            "start_time": entry["start_time"],
            "end_time": entry["end_time"],
        })

print(json.dumps(output, ensure_ascii=False))