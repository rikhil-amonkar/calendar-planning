# SOLUTION:
import json
from copy import deepcopy

def minutes(h, m):
    return h * 60 + m

def parse_time_24(s):
    # expects 'H:MM' or 'HH:MM' 24-hour
    h, m = s.split(':')
    return int(h) * 60 + int(m)

def fmt_time(mins):
    h = mins // 60
    m = mins % 60
    return f"{h}:{m:02d}"

def build_travel_times():
    # Directed travel times (in minutes)
    GGP = "Golden Gate Park"
    HA = "Haight-Ashbury"
    FW = "Fisherman's Wharf"
    TC = "The Castro"
    CT = "Chinatown"
    AS = "Alamo Square"
    NB = "North Beach"
    RH = "Russian Hill"

    travel = {
        GGP: {HA:7, FW:24, TC:13, CT:23, AS:10, NB:24, RH:19},
        HA:  {GGP:7, FW:23, TC:6, CT:19, AS:5, NB:19, RH:17},
        FW:  {GGP:25, HA:22, TC:26, CT:12, AS:20, NB:6, RH:7},
        TC:  {GGP:11, HA:6, FW:24, CT:20, AS:8, NB:20, RH:18},
        CT:  {GGP:23, HA:19, FW:8, TC:22, AS:17, NB:3, RH:7},
        AS:  {GGP:9, HA:5, FW:19, TC:8, CT:16, NB:15, RH:13},
        NB:  {GGP:22, HA:18, FW:5, TC:22, CT:6, AS:16, RH:4},
        RH:  {GGP:21, HA:17, FW:7, TC:21, CT:9, AS:15, NB:5},
    }
    return travel

def main():
    # Locations
    GGP = "Golden Gate Park"
    HA = "Haight-Ashbury"
    FW = "Fisherman's Wharf"
    TC = "The Castro"
    CT = "Chinatown"
    AS = "Alamo Square"
    NB = "North Beach"
    RH = "Russian Hill"

    # Start time and location
    start_location = GGP
    start_time = parse_time_24("9:00")

    # Meeting constraints (24-hour times)
    friends = [
        {"name": "Carol", "location": HA, "window_start": parse_time_24("21:30"), "window_end": parse_time_24("22:30"), "min_duration": 60},
        {"name": "Laura", "location": FW, "window_start": parse_time_24("11:45"), "window_end": parse_time_24("21:30"), "min_duration": 60},
        {"name": "Karen", "location": TC, "window_start": parse_time_24("7:15"), "window_end": parse_time_24("14:00"), "min_duration": 75},
        {"name": "Elizabeth", "location": CT, "window_start": parse_time_24("12:15"), "window_end": parse_time_24("21:30"), "min_duration": 75},
        {"name": "Deborah", "location": AS, "window_start": parse_time_24("12:00"), "window_end": parse_time_24("15:00"), "min_duration": 105},
        {"name": "Jason", "location": NB, "window_start": parse_time_24("14:45"), "window_end": parse_time_24("19:00"), "min_duration": 90},
        {"name": "Steven", "location": RH, "window_start": parse_time_24("14:45"), "window_end": parse_time_24("18:30"), "min_duration": 120},
    ]

    # Travel times
    travel = build_travel_times()

    # DFS search to maximize number of meetings; tie-breakers: minimize non-meeting time (travel + waiting), then earliest end time
    best = {
        "schedule": [],
        "count": 0,
        "non_meeting": float('inf'),
        "end_time": float('inf'),
        "travel": 0,
        "wait": 0
    }

    # Sort friends by window_end then by window_start to guide search
    friends_sorted = sorted(friends, key=lambda f: (f["window_end"], f["window_start"], f["name"]))

    def try_meet(current_loc, current_time, person):
        # returns (start, end, travel_time, wait_time) if feasible, else None
        if current_loc not in travel or person["location"] not in travel[current_loc]:
            return None
        t_travel = travel[current_loc][person["location"]]
        arrival = current_time + t_travel
        start = max(arrival, person["window_start"])
        end = start + person["min_duration"]
        if end <= person["window_end"]:
            wait = max(0, start - arrival)
            return (start, end, t_travel, wait)
        return None

    def is_better(cand, best):
        if cand["count"] > best["count"]:
            return True
        if cand["count"] < best["count"]:
            return False
        # Tie-break by less non-meeting time
        if cand["non_meeting"] < best["non_meeting"]:
            return True
        if cand["non_meeting"] > best["non_meeting"]:
            return False
        # Then earlier end time
        if cand["end_time"] < best["end_time"]:
            return True
        if cand["end_time"] > best["end_time"]:
            return False
        # Then less travel time
        if cand["travel"] < best["travel"]:
            return True
        if cand["travel"] > best["travel"]:
            return False
        # Then less wait time
        if cand["wait"] < best["wait"]:
            return True
        return False

    def dfs(current_loc, current_time, remaining, schedule, acc_travel, acc_wait):
        nonlocal best

        # Update best with current partial schedule
        cand = {
            "schedule": deepcopy(schedule),
            "count": len(schedule),
            "non_meeting": acc_travel + acc_wait,
            "end_time": current_time if schedule else start_time,
            "travel": acc_travel,
            "wait": acc_wait
        }
        if is_better(cand, best):
            best = cand

        # Potential pruning: if even meeting all remaining can't beat best, stop
        if len(schedule) + len(remaining) <= best["count"]:
            return

        # Iterate through remaining friends
        for idx, person in enumerate(remaining):
            res = try_meet(current_loc, current_time, person)
            if res is None:
                continue
            start, end, t_travel, t_wait = res
            new_event = {
                "action": "meet",
                "location": person["location"],
                "person": person["name"],
                "start_time": start,
                "end_time": end
            }
            schedule.append(new_event)
            new_remaining = remaining[:idx] + remaining[idx+1:]
            dfs(person["location"], end, new_remaining, schedule, acc_travel + t_travel, acc_wait + t_wait)
            schedule.pop()

    dfs(start_location, start_time, friends_sorted, [], 0, 0)

    # Build output JSON
    itinerary = []
    for evt in best["schedule"]:
        itinerary.append({
            "action": "meet",
            "location": evt["location"],
            "person": evt["person"],
            "start_time": fmt_time(evt["start_time"]),
            "end_time": fmt_time(evt["end_time"])
        })

    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()