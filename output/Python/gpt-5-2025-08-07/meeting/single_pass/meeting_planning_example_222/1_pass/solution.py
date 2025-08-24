# SOLUTION:
import json
import itertools

def time_to_minutes(t_str):
    # expects 'H:MM' or 'HH:MM' 24-hour
    h, m = map(int, t_str.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

def plan_schedule(start_loc, start_time, people, travel_time):
    # Try all subsets (size 3 to 1) and permutations; choose best by:
    # 1) maximize number of friends met
    # 2) tie-breaker: maximize total meeting time
    # 3) then minimize total travel time
    # 4) then minimize finish time
    best = None

    # Prepare sizes descending
    for r in range(len(people), 0, -1):
        found_for_size = []
        for subset in itertools.combinations(people, r):
            for order in itertools.permutations(subset):
                sched = compute_schedule_for_order(start_loc, start_time, order, travel_time)
                if sched is not None:
                    found_for_size.append(sched)
        if found_for_size:
            # Pick the best among this size
            found_for_size.sort(key=lambda s: (
                -len(s["meetings"]),
                -s["total_meeting_time"],
                s["total_travel_time"],
                s["finish_time"],
            ))
            best = found_for_size[0]
            break
    return best

def compute_schedule_for_order(start_loc, start_time, order, travel_time):
    n = len(order)
    # Forward earliest schedule with minimal durations
    earliest_start = [None]*n
    earliest_end_min = [None]*n
    locs = [p["location"] for p in order]
    mins = [p["min_duration"] for p in order]
    avail_starts = [p["avail_start"] for p in order]
    avail_ends = [p["avail_end"] for p in order]

    prev_end = start_time
    prev_loc = start_loc
    total_travel = 0

    for i in range(n):
        tt = travel_time[(prev_loc, locs[i])]
        total_travel += tt
        arrive = prev_end + tt
        s = max(arrive, avail_starts[i])
        e_min = s + mins[i]
        if e_min > avail_ends[i]:
            return None  # infeasible
        earliest_start[i] = s
        earliest_end_min[i] = e_min
        prev_end = e_min
        prev_loc = locs[i]

    # Backward latest feasible finishes
    latest_finish = [None]*n
    latest_start = [None]*n

    latest_finish[-1] = avail_ends[-1]
    latest_start[-1] = latest_finish[-1] - mins[-1]

    for i in range(n-2, -1, -1):
        tt = travel_time[(locs[i], locs[i+1])]
        latest_finish[i] = min(avail_ends[i], latest_start[i+1] - tt)
        latest_start[i] = latest_finish[i] - mins[i]

    # Feasibility check with earliest starts
    for i in range(n):
        if earliest_start[i] > latest_start[i]:
            return None

    # Build final maximized-duration schedule: start at max arrival/avail, end at latest_finish
    meetings = []
    prev_end = start_time
    prev_loc = start_loc
    for i in range(n):
        tt = travel_time[(prev_loc, locs[i])]
        arrive = prev_end + tt
        s = max(arrive, avail_starts[i])
        e = latest_finish[i]
        # Safety check
        if e < s + mins[i]:
            return None
        meetings.append({
            "person": order[i]["name"],
            "location": locs[i],
            "start": s,
            "end": e,
        })
        prev_end = e
        prev_loc = locs[i]

    total_meeting_time = sum(m["end"] - m["start"] for m in meetings)
    finish_time = meetings[-1]["end"] if meetings else start_time

    return {
        "meetings": meetings,
        "total_meeting_time": total_meeting_time,
        "total_travel_time": total_travel,
        "finish_time": finish_time,
    }

def main():
    # Input variables (constraints)
    start_location = "Nob Hill"
    start_time_str = "9:00"

    people = [
        {
            "name": "Helen",
            "location": "North Beach",
            "avail_start_str": "7:00",
            "avail_end_str": "16:45",
            "min_duration": 120
        },
        {
            "name": "Kimberly",
            "location": "Fisherman's Wharf",
            "avail_start_str": "16:30",
            "avail_end_str": "21:00",
            "min_duration": 45
        },
        {
            "name": "Patricia",
            "location": "Bayview",
            "avail_start_str": "18:00",
            "avail_end_str": "21:15",
            "min_duration": 120
        },
    ]

    # Convert times to minutes
    for p in people:
        p["avail_start"] = time_to_minutes(p["avail_start_str"])
        p["avail_end"] = time_to_minutes(p["avail_end_str"])

    start_time = time_to_minutes(start_time_str)

    # Travel times (directed, in minutes)
    travel_time = {
        ("Nob Hill", "North Beach"): 8,
        ("Nob Hill", "Fisherman's Wharf"): 11,
        ("Nob Hill", "Bayview"): 19,
        ("North Beach", "Nob Hill"): 7,
        ("North Beach", "Fisherman's Wharf"): 5,
        ("North Beach", "Bayview"): 22,
        ("Fisherman's Wharf", "Nob Hill"): 11,
        ("Fisherman's Wharf", "North Beach"): 6,
        ("Fisherman's Wharf", "Bayview"): 26,
        ("Bayview", "Nob Hill"): 20,
        ("Bayview", "North Beach"): 21,
        ("Bayview", "Fisherman's Wharf"): 25,
    }

    # Compute optimal schedule
    result = plan_schedule(start_location, start_time, people, travel_time)

    # Format output JSON
    itinerary = []
    if result and result["meetings"]:
        for m in result["meetings"]:
            itinerary.append({
                "action": "meet",
                "location": m["location"],
                "person": m["person"],
                "start_time": minutes_to_time(m["start"]),
                "end_time": minutes_to_time(m["end"]),
            })

    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()