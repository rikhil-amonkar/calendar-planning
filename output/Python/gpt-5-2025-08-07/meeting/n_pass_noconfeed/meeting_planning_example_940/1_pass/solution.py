"""
SOLUTION:
"""
import json

def hm(h, m):
    return h * 60 + m

def tstr(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

def main():
    # Travel times (minutes)
    travel = {
        "Union Square": {
            "Mission District": 14,
            "Fisherman's Wharf": 15,
            "Russian Hill": 13,
            "Marina District": 18,
            "North Beach": 10,
            "Chinatown": 7,
            "Pacific Heights": 15,
            "The Castro": 17,
            "Nob Hill": 9,
            "Sunset District": 27,
        },
        "Mission District": {
            "Union Square": 15,
            "Fisherman's Wharf": 22,
            "Russian Hill": 15,
            "Marina District": 19,
            "North Beach": 17,
            "Chinatown": 16,
            "Pacific Heights": 16,
            "The Castro": 7,
            "Nob Hill": 12,
            "Sunset District": 24,
        },
        "Fisherman's Wharf": {
            "Union Square": 13,
            "Mission District": 22,
            "Russian Hill": 7,
            "Marina District": 9,
            "North Beach": 6,
            "Chinatown": 12,
            "Pacific Heights": 12,
            "The Castro": 27,
            "Nob Hill": 11,
            "Sunset District": 27,
        },
        "Russian Hill": {
            "Union Square": 10,
            "Mission District": 16,
            "Fisherman's Wharf": 7,
            "Marina District": 7,
            "North Beach": 5,
            "Chinatown": 9,
            "Pacific Heights": 7,
            "The Castro": 21,
            "Nob Hill": 5,
            "Sunset District": 23,
        },
        "Marina District": {
            "Union Square": 16,
            "Mission District": 20,
            "Fisherman's Wharf": 10,
            "Russian Hill": 8,
            "North Beach": 11,
            "Chinatown": 15,
            "Pacific Heights": 7,
            "The Castro": 22,
            "Nob Hill": 12,
            "Sunset District": 19,
        },
        "North Beach": {
            "Union Square": 7,
            "Mission District": 18,
            "Fisherman's Wharf": 5,
            "Russian Hill": 4,
            "Marina District": 9,
            "Chinatown": 6,
            "Pacific Heights": 8,
            "The Castro": 23,
            "Nob Hill": 7,
            "Sunset District": 27,
        },
        "Chinatown": {
            "Union Square": 7,
            "Mission District": 17,
            "Fisherman's Wharf": 8,
            "Russian Hill": 7,
            "Marina District": 12,
            "North Beach": 3,
            "Pacific Heights": 10,
            "The Castro": 22,
            "Nob Hill": 9,
            "Sunset District": 29,
        },
        "Pacific Heights": {
            "Union Square": 12,
            "Mission District": 15,
            "Fisherman's Wharf": 13,
            "Russian Hill": 7,
            "Marina District": 6,
            "North Beach": 9,
            "Chinatown": 11,
            "The Castro": 16,
            "Nob Hill": 8,
            "Sunset District": 21,
        },
        "The Castro": {
            "Union Square": 19,
            "Mission District": 7,
            "Fisherman's Wharf": 24,
            "Russian Hill": 18,
            "Marina District": 21,
            "North Beach": 20,
            "Chinatown": 22,
            "Pacific Heights": 16,
            "Nob Hill": 16,
            "Sunset District": 17,
        },
        "Nob Hill": {
            "Union Square": 7,
            "Mission District": 13,
            "Fisherman's Wharf": 10,
            "Russian Hill": 5,
            "Marina District": 11,
            "North Beach": 8,
            "Chinatown": 6,
            "Pacific Heights": 8,
            "The Castro": 17,
            "Sunset District": 24,
        },
        "Sunset District": {
            "Union Square": 30,
            "Mission District": 25,
            "Fisherman's Wharf": 29,
            "Russian Hill": 24,
            "Marina District": 21,
            "North Beach": 28,
            "Chinatown": 30,
            "Pacific Heights": 21,
            "The Castro": 17,
            "Nob Hill": 27,
        },
    }

    # add zero travel to self
    locations = list(travel.keys())
    for a in locations:
        travel[a][a] = 0

    # Friends and constraints
    friends = [
        {"name": "Kevin", "location": "Mission District", "start": hm(20, 45), "end": hm(21, 45), "min_duration": 60},
        {"name": "Mark", "location": "Fisherman's Wharf", "start": hm(17, 15), "end": hm(20, 0), "min_duration": 90},
        {"name": "Jessica", "location": "Russian Hill", "start": hm(9, 0), "end": hm(15, 0), "min_duration": 120},
        {"name": "Jason", "location": "Marina District", "start": hm(15, 15), "end": hm(21, 45), "min_duration": 120},
        {"name": "John", "location": "North Beach", "start": hm(9, 45), "end": hm(18, 0), "min_duration": 15},
        {"name": "Karen", "location": "Chinatown", "start": hm(16, 45), "end": hm(19, 0), "min_duration": 75},
        {"name": "Sarah", "location": "Pacific Heights", "start": hm(17, 30), "end": hm(18, 15), "min_duration": 45},
        {"name": "Amanda", "location": "The Castro", "start": hm(20, 0), "end": hm(21, 15), "min_duration": 60},
        {"name": "Nancy", "location": "Nob Hill", "start": hm(9, 45), "end": hm(13, 0), "min_duration": 45},
        {"name": "Rebecca", "location": "Sunset District", "start": hm(8, 45), "end": hm(15, 0), "min_duration": 75},
    ]

    name_to_idx = {f["name"]: i for i, f in enumerate(friends)}

    start_location = "Union Square"
    start_time = hm(9, 0)

    # Memoization: earliest time we've reached a given (location, met_mask)
    memo = {}

    best_result = {
        "count": -1,
        "end_time": 10**9,
        "travel_time": 10**9,
        "itinerary": [],
    }

    total = len(friends)
    all_indices = list(range(total))

    # Precompute an order to try friends earlier windows first (heuristic)
    order = sorted(all_indices, key=lambda i: (friends[i]["end"], friends[i]["start"]))

    def bitcount(x):
        return x.bit_count() if hasattr(int, "bit_count") else bin(x).count("1")

    def dfs(curr_loc, curr_time, met_mask, itinerary, total_travel):
        nonlocal best_result

        cnt = bitcount(met_mask)
        # Update best if improved
        if (cnt > best_result["count"]) or (
            cnt == best_result["count"] and (curr_time < best_result["end_time"] or
                                             (curr_time == best_result["end_time"] and total_travel < best_result["travel_time"]))
        ):
            best_result = {
                "count": cnt,
                "end_time": curr_time,
                "travel_time": total_travel,
                "itinerary": itinerary[:],
            }

        # Simple upper bound prune
        remaining = total - cnt
        if cnt + remaining < best_result["count"]:
            return

        # Try scheduling each remaining friend
        for i in order:
            if met_mask & (1 << i):
                continue
            f = friends[i]
            # Check travel feasibility
            if curr_loc not in travel or f["location"] not in travel[curr_loc]:
                continue
            arrive = curr_time + travel[curr_loc][f["location"]]
            start_meet = max(arrive, f["start"])
            end_meet = start_meet + f["min_duration"]
            if end_meet > f["end"]:
                continue

            new_mask = met_mask | (1 << i)
            state_key = (f["location"], new_mask)
            # Memo prune: keep earliest end time at this (loc, mask)
            prev_best_time = memo.get(state_key)
            if prev_best_time is not None and prev_best_time <= end_meet:
                continue
            memo[state_key] = end_meet

            itinerary.append({
                "action": "meet",
                "location": f["location"],
                "person": f["name"],
                "start_time": tstr(start_meet),
                "end_time": tstr(end_meet),
            })
            dfs(
                f["location"],
                end_meet,
                new_mask,
                itinerary,
                total_travel + travel[curr_loc][f["location"]],
            )
            itinerary.pop()

    dfs(start_location, start_time, 0, [], 0)

    output = {
        "itinerary": best_result["itinerary"]
    }
    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()