import itertools
import json
from typing import List, Dict, Tuple, Optional

# ---------------------------
# Input variables
# ---------------------------
start_location = "Golden Gate Park"
start_time_str = "9:00"

# Travel times in minutes (directed)
travel = {
    "Golden Gate Park": {
        "Alamo Square": 10,
        "Presidio": 11,
        "Russian Hill": 19,
    },
    "Alamo Square": {
        "Golden Gate Park": 9,
        "Presidio": 18,
        "Russian Hill": 13,
    },
    "Presidio": {
        "Golden Gate Park": 12,
        "Alamo Square": 18,
        "Russian Hill": 14,
    },
    "Russian Hill": {
        "Golden Gate Park": 21,
        "Alamo Square": 15,
        "Presidio": 14,
    },
}

friends = [
    {
        "name": "Timothy",
        "location": "Alamo Square",
        "window_start": "12:00",
        "window_end": "16:15",
        "min_duration": 105,
    },
    {
        "name": "Mark",
        "location": "Presidio",
        "window_start": "18:45",
        "window_end": "21:00",
        "min_duration": 60,
    },
    {
        "name": "Joseph",
        "location": "Russian Hill",
        "window_start": "16:45",
        "window_end": "21:30",
        "min_duration": 60,
    },
]

# ---------------------------
# Helpers
# ---------------------------
def parse_time(t: str) -> int:
    # format "H:MM" or "HH:MM" 24-hour, no leading zero required
    h, m = t.split(":")
    return int(h) * 60 + int(m)

def fmt_time(minutes: int) -> str:
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def build_friends_struct(friends_input):
    res = []
    for f in friends_input:
        res.append({
            "name": f["name"],
            "location": f["location"],
            "start": parse_time(f["window_start"]),
            "end": parse_time(f["window_end"]),
            "min_dur": f["min_duration"],
        })
    return res

# ---------------------------
# Core scheduling search
# ---------------------------
start_time = parse_time(start_time_str)
friends_data = build_friends_struct(friends)

def schedule_order(order: List[Dict]) -> Optional[Dict]:
    best = None  # dict with keys: itinerary, final_end, total_travel, total_meeting, idle, count

    def update_best(itinerary: List[Dict], total_travel: int):
        nonlocal best
        if not itinerary:
            return
        final_end = itinerary[-1]["end"]
        total_meeting = sum(meet["end"] - meet["start"] for meet in itinerary)
        idle = (final_end - start_time) - total_meeting - total_travel
        count = len(itinerary)
        candidate = {
            "itinerary": itinerary,
            "final_end": final_end,
            "total_travel": total_travel,
            "total_meeting": total_meeting,
            "idle": idle,
            "count": count,
        }
        if best is None:
            best = candidate
            return
        # Compare: maximize count, then minimize idle, then minimize final_end
        if (candidate["count"] > best["count"] or
            (candidate["count"] == best["count"] and candidate["idle"] < best["idle"]) or
            (candidate["count"] == best["count"] and candidate["idle"] == best["idle"] and candidate["final_end"] < best["final_end"])):
            best = candidate

    def rec(idx: int, curr_loc: str, curr_time: int, travel_total: int, meetings: List[Dict]):
        if idx == len(order):
            update_best(meetings, travel_total)
            return

        p = order[idx]
        t_move = travel[curr_loc][p["location"]]
        earliest_arrival = curr_time + t_move
        earliest_start = max(p["start"], earliest_arrival)
        latest_start = p["end"] - p["min_dur"]
        if earliest_start > latest_start:
            return

        next_p = order[idx + 1] if idx + 1 < len(order) else None
        t_to_next = travel[p["location"]][next_p["location"]] if next_p else None

        # Candidate start times: earliest, latest, and an alignment option toward next start (if applicable)
        start_candidates = {earliest_start, latest_start}
        if next_p:
            s_align = next_p["start"] - t_to_next - p["min_dur"]
            s_align = max(earliest_start, min(s_align, latest_start))
            start_candidates.add(s_align)

        for start in sorted(start_candidates):
            base_end = start + p["min_dur"]
            # Candidate end times: minimum required, alignment to arrive at next start exactly, and latest possible
            end_candidates = set()
            end_candidates.add(base_end)
            if next_p:
                e_align = next_p["start"] - t_to_next
                if e_align >= base_end:
                    end_candidates.add(min(e_align, p["end"]))
            end_candidates.add(p["end"])
            valid_endings = sorted(e for e in end_candidates if base_end <= e <= p["end"])

            for end in valid_endings:
                meet_entry = {
                    "action": "meet",
                    "location": p["location"],
                    "person": p["name"],
                    "start": start,
                    "end": end,
                }
                rec(idx + 1, p["location"], end, travel_total + t_move, meetings + [meet_entry])

    rec(0, start_location, start_time, 0, [])
    return best

def plan():
    best_overall = None
    # Evaluate all subsets by decreasing size to maximize number of friends met
    for r in range(len(friends_data), 0, -1):
        found_for_size = None
        for perm in itertools.permutations(friends_data, r):
            result = schedule_order(list(perm))
            if result is None:
                continue
            # Update best for this subset size
            if found_for_size is None:
                found_for_size = result
            else:
                # same comparison logic
                a, b = result, found_for_size
                if (a["count"] > b["count"] or
                    (a["count"] == b["count"] and a["idle"] < b["idle"]) or
                    (a["count"] == b["count"] and a["idle"] == b["idle"] and a["final_end"] < b["final_end"])):
                    found_for_size = a
        if found_for_size:
            best_overall = found_for_size
            break  # since we iterate from largest subset size downwards

    if best_overall is None:
        return {"itinerary": []}

    # Format itinerary times
    formatted_itinerary = []
    for item in best_overall["itinerary"]:
        formatted_itinerary.append({
            "action": "meet",
            "location": item["location"],
            "person": item["person"],
            "start_time": fmt_time(item["start"]),
            "end_time": fmt_time(item["end"]),
        })

    return {"itinerary": formatted_itinerary}

if __name__ == "__main__":
    result = plan()
    print(json.dumps(result, ensure_ascii=False))