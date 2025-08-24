import json

def minutes(h, m):
    return h * 60 + m

def fmt_time(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

def build_data():
    # Travel times in minutes (directed)
    tt = {
        "The Castro": {
            "Alamo Square": 8,
            "Richmond District": 16,
            "Financial District": 21,
            "Union Square": 19,
            "Fisherman's Wharf": 24,
            "Marina District": 21,
            "Haight-Ashbury": 6,
            "Mission District": 7,
            "Pacific Heights": 16,
            "Golden Gate Park": 11,
        },
        "Alamo Square": {
            "The Castro": 8,
            "Richmond District": 11,
            "Financial District": 17,
            "Union Square": 14,
            "Fisherman's Wharf": 19,
            "Marina District": 15,
            "Haight-Ashbury": 5,
            "Mission District": 10,
            "Pacific Heights": 10,
            "Golden Gate Park": 9,
        },
        "Richmond District": {
            "The Castro": 16,
            "Alamo Square": 13,
            "Financial District": 22,
            "Union Square": 21,
            "Fisherman's Wharf": 18,
            "Marina District": 9,
            "Haight-Ashbury": 10,
            "Mission District": 20,
            "Pacific Heights": 10,
            "Golden Gate Park": 9,
        },
        "Financial District": {
            "The Castro": 20,
            "Alamo Square": 17,
            "Richmond District": 21,
            "Union Square": 9,
            "Fisherman's Wharf": 10,
            "Marina District": 15,
            "Haight-Ashbury": 19,
            "Mission District": 17,
            "Pacific Heights": 13,
            "Golden Gate Park": 23,
        },
        "Union Square": {
            "The Castro": 17,
            "Alamo Square": 15,
            "Richmond District": 20,
            "Financial District": 9,
            "Fisherman's Wharf": 15,
            "Marina District": 18,
            "Haight-Ashbury": 18,
            "Mission District": 14,
            "Pacific Heights": 15,
            "Golden Gate Park": 22,
        },
        "Fisherman's Wharf": {
            "The Castro": 27,
            "Alamo Square": 21,
            "Richmond District": 18,
            "Financial District": 11,
            "Union Square": 13,
            "Marina District": 9,
            "Haight-Ashbury": 22,
            "Mission District": 22,
            "Pacific Heights": 12,
            "Golden Gate Park": 25,
        },
        "Marina District": {
            "The Castro": 22,
            "Alamo Square": 15,
            "Richmond District": 11,
            "Financial District": 17,
            "Union Square": 16,
            "Fisherman's Wharf": 10,
            "Haight-Ashbury": 16,
            "Mission District": 20,
            "Pacific Heights": 7,
            "Golden Gate Park": 18,
        },
        "Haight-Ashbury": {
            "The Castro": 6,
            "Alamo Square": 5,
            "Richmond District": 10,
            "Financial District": 21,
            "Union Square": 19,
            "Fisherman's Wharf": 23,
            "Marina District": 17,
            "Mission District": 11,
            "Pacific Heights": 12,
            "Golden Gate Park": 7,
        },
        "Mission District": {
            "The Castro": 7,
            "Alamo Square": 11,
            "Richmond District": 20,
            "Financial District": 15,
            "Union Square": 15,
            "Fisherman's Wharf": 22,
            "Marina District": 19,
            "Haight-Ashbury": 12,
            "Pacific Heights": 16,
            "Golden Gate Park": 17,
        },
        "Pacific Heights": {
            "The Castro": 16,
            "Alamo Square": 10,
            "Richmond District": 12,
            "Financial District": 13,
            "Union Square": 12,
            "Fisherman's Wharf": 13,
            "Marina District": 6,
            "Haight-Ashbury": 11,
            "Mission District": 15,
            "Golden Gate Park": 15,
        },
        "Golden Gate Park": {
            "The Castro": 13,
            "Alamo Square": 9,
            "Richmond District": 7,
            "Financial District": 26,
            "Union Square": 22,
            "Fisherman's Wharf": 24,
            "Marina District": 16,
            "Haight-Ashbury": 7,
            "Mission District": 17,
            "Pacific Heights": 16,
        },
    }

    # Friends with constraints
    friends = [
        {
            "person": "William",
            "location": "Alamo Square",
            "start": minutes(15, 15),
            "end": minutes(17, 15),
            "min_duration": 60,
        },
        {
            "person": "Joshua",
            "location": "Richmond District",
            "start": minutes(7, 0),
            "end": minutes(20, 0),
            "min_duration": 15,
        },
        {
            "person": "Joseph",
            "location": "Financial District",
            "start": minutes(11, 15),
            "end": minutes(13, 30),
            "min_duration": 15,
        },
        {
            "person": "David",
            "location": "Union Square",
            "start": minutes(16, 45),
            "end": minutes(19, 15),
            "min_duration": 45,
        },
        {
            "person": "Brian",
            "location": "Fisherman's Wharf",
            "start": minutes(13, 45),
            "end": minutes(20, 45),
            "min_duration": 105,
        },
        {
            "person": "Karen",
            "location": "Marina District",
            "start": minutes(11, 30),
            "end": minutes(18, 30),
            "min_duration": 15,
        },
        {
            "person": "Anthony",
            "location": "Haight-Ashbury",
            "start": minutes(7, 15),
            "end": minutes(10, 30),
            "min_duration": 30,
        },
        {
            "person": "Matthew",
            "location": "Mission District",
            "start": minutes(17, 15),
            "end": minutes(19, 15),
            "min_duration": 120,
        },
        {
            "person": "Helen",
            "location": "Pacific Heights",
            "start": minutes(8, 0),
            "end": minutes(12, 0),
            "min_duration": 75,
        },
        {
            "person": "Jeffrey",
            "location": "Golden Gate Park",
            "start": minutes(19, 0),
            "end": minutes(21, 30),
            "min_duration": 60,
        },
    ]

    return tt, friends

def search_optimal_schedule(travel, friends, start_loc, start_time):
    n = len(friends)
    idx_map = {friends[i]["person"]: i for i in range(n)}

    # Precompute an order for stable iteration (by window start)
    order = sorted(range(n), key=lambda i: (friends[i]["start"], friends[i]["end"]))

    best = {
        "count": 0,
        "end_time": start_time,
        "total_travel": 0,
        "itinerary": [],
        "mask": 0,
    }

    # Simple cache to prune dominated states: key -> best (count, -end_time) seen
    from functools import lru_cache

    @lru_cache(maxsize=None)
    def dfs(current_loc, current_time, mask, total_travel):
        # Compute optimistic bound
        remaining_possible = 0
        for i in range(n):
            if not (mask & (1 << i)):
                f = friends[i]
                # optimistic: zero travel
                earliest_start = max(current_time, f["start"])
                if earliest_start + f["min_duration"] <= f["end"]:
                    remaining_possible += 1

        best_local = (0, current_time, total_travel, [])  # count, end_time, total_travel, itin

        # Try all feasible next meetings, sorted by earliest feasible finish
        candidates = []
        for i in order:
            if mask & (1 << i):
                continue
            f = friends[i]
            if current_loc not in travel or f["location"] not in travel[current_loc]:
                continue
            arr = current_time + travel[current_loc][f["location"]]
            start = max(arr, f["start"])
            end = start + f["min_duration"]
            if end <= f["end"]:
                candidates.append((end, start, i, arr))

        candidates.sort()  # by earliest finish time

        if not candidates:
            return best_local

        # Branch over candidates
        local_best_tuple = (-1, float('inf'), float('inf'))  # (count, end_time, total_travel)
        local_best = best_local

        for end, start, i, arr in candidates:
            f = friends[i]
            new_mask = mask | (1 << i)
            meet_record = {
                "action": "meet",
                "location": f["location"],
                "person": f["person"],
                "start_time": start,
                "end_time": end,
            }
            # Accumulate travel time (arr - current_time)
            new_total_travel = total_travel + (arr - current_time if arr > current_time else 0)

            sub_count, sub_end_time, sub_total_travel, sub_itin = dfs(
                f["location"], end, new_mask, new_total_travel
            )

            # Include current meeting
            count = 1 + sub_count
            end_time_res = sub_end_time
            total_travel_res = sub_total_travel

            # Tie-breakers: maximize count, then minimize end_time, then minimize total_travel
            cand_tuple = (count, -end_time_res, -total_travel_res)
            best_tuple = (local_best_tuple[0], -local_best_tuple[1], -local_best_tuple[2]) if local_best_tuple[0] != -1 else None

            if best_tuple is None or cand_tuple > best_tuple:
                local_best_tuple = (count, end_time_res, total_travel_res)
                local_best = (count, end_time_res, total_travel_res, [meet_record] + sub_itin)

        return local_best

    count, end_time, total_travel, itin = dfs(start_loc, start_time, 0, 0)

    # Convert times to strings
    itinerary_out = []
    for rec in itin:
        itinerary_out.append({
            "action": "meet",
            "location": rec["location"],
            "person": rec["person"],
            "start_time": fmt_time(rec["start_time"]),
            "end_time": fmt_time(rec["end_time"]),
        })

    return {"itinerary": itinerary_out}

def main():
    travel, friends = build_data()
    start_loc = "The Castro"
    start_time = minutes(9, 0)  # 9:00

    result = search_optimal_schedule(travel, friends, start_loc, start_time)
    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    # SOLUTION:
    main()