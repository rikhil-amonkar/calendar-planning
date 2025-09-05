import json
from itertools import permutations

def to_minutes(h, m):
    return h * 60 + m

def parse_time(s):
    # Not used, but kept for completeness if needed
    s = s.strip().upper()
    pm = "PM" in s
    s = s.replace("AM", "").replace("PM", "").strip()
    h, m = map(int, s.split(":"))
    if h == 12:
        h = 0
    if pm:
        h += 12
    return h * 60 + m

def time_str(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def get_travel_time(a, b, travel):
    return travel[a][b]

def feasible_next(current_loc, current_time, person, travel):
    travel_time = get_travel_time(current_loc, person["location"], travel)
    arrival = current_time + travel_time
    start = max(arrival, person["start"])
    end = start + person["min_duration"]
    if end <= person["end"]:
        return {
            "start": start,
            "end": end,
            "arrival": arrival,
            "travel_time": travel_time
        }
    return None

def search_best(start_loc, start_time, people, travel):
    names = [p["name"] for p in people]
    people_by_name = {p["name"]: p for p in people}

    best_solution = {
        "count": 0,
        "total_meet": 0,
        "end_time": start_time,
        "total_travel": 0,
        "path": []
    }

    # DFS with backtracking
    def dfs(current_loc, current_time, remaining_names, path, total_meet, total_travel):
        nonlocal best_solution

        # Evaluate current partial solution
        current_count = len(path)
        # Update best if better by (count, total_meet, -end_time, -total_travel)
        is_better = False
        if current_count > best_solution["count"]:
            is_better = True
        elif current_count == best_solution["count"]:
            if total_meet > best_solution["total_meet"]:
                is_better = True
            elif total_meet == best_solution["total_meet"]:
                if current_time < best_solution["end_time"]:
                    is_better = True
                elif current_time == best_solution["end_time"]:
                    if total_travel < best_solution["total_travel"]:
                        is_better = True
        if is_better:
            best_solution = {
                "count": current_count,
                "total_meet": total_meet,
                "end_time": current_time,
                "total_travel": total_travel,
                "path": list(path)
            }

        # If no one left, return
        if not remaining_names:
            return

        # Prune if even meeting all remaining cannot beat current best in count
        if current_count + len(remaining_names) < best_solution["count"]:
            return

        # Try each remaining person as next meeting
        for name in remaining_names:
            person = people_by_name[name]
            feas = feasible_next(current_loc, current_time, person, travel)
            if feas is None:
                continue
            # Schedule minimal feasible meeting
            meeting_entry = {
                "action": "meet",
                "location": person["location"],
                "person": person["name"],
                "start_time": feas["start"],
                "end_time": feas["end"]
            }
            new_remaining = [n for n in remaining_names if n != name]
            path.append(meeting_entry)
            dfs(
                person["location"],
                feas["end"],
                new_remaining,
                path,
                total_meet + person["min_duration"],
                total_travel + feas["travel_time"]
            )
            path.pop()

    dfs(start_loc, start_time, names, [], 0, 0)
    return best_solution

def main():
    # Locations and directed travel times (in minutes)
    travel = {
        "Russian Hill": {
            "Presidio": 14,
            "Chinatown": 9,
            "Pacific Heights": 7,
            "Richmond District": 14,
            "Fisherman's Wharf": 7,
            "Golden Gate Park": 21,
            "Bayview": 23,
        },
        "Presidio": {
            "Russian Hill": 14,
            "Chinatown": 21,
            "Pacific Heights": 11,
            "Richmond District": 7,
            "Fisherman's Wharf": 19,
            "Golden Gate Park": 12,
            "Bayview": 31,
        },
        "Chinatown": {
            "Russian Hill": 7,
            "Presidio": 19,
            "Pacific Heights": 10,
            "Richmond District": 20,
            "Fisherman's Wharf": 8,
            "Golden Gate Park": 23,
            "Bayview": 22,
        },
        "Pacific Heights": {
            "Russian Hill": 7,
            "Presidio": 11,
            "Chinatown": 11,
            "Richmond District": 12,
            "Fisherman's Wharf": 13,
            "Golden Gate Park": 15,
            "Bayview": 22,
        },
        "Richmond District": {
            "Russian Hill": 13,
            "Presidio": 7,
            "Chinatown": 20,
            "Pacific Heights": 10,
            "Fisherman's Wharf": 18,
            "Golden Gate Park": 9,
            "Bayview": 26,
        },
        "Fisherman's Wharf": {
            "Russian Hill": 7,
            "Presidio": 17,
            "Chinatown": 12,
            "Pacific Heights": 12,
            "Richmond District": 18,
            "Golden Gate Park": 25,
            "Bayview": 26,
        },
        "Golden Gate Park": {
            "Russian Hill": 19,
            "Presidio": 11,
            "Chinatown": 23,
            "Pacific Heights": 16,
            "Richmond District": 7,
            "Fisherman's Wharf": 24,
            "Bayview": 23,
        },
        "Bayview": {
            "Russian Hill": 23,
            "Presidio": 31,
            "Chinatown": 18,
            "Pacific Heights": 23,
            "Richmond District": 25,
            "Fisherman's Wharf": 25,
            "Golden Gate Park": 22,
        },
    }

    # Input parameters
    start_location = "Russian Hill"
    start_time = to_minutes(9, 0)

    people = [
        {
            "name": "Matthew",
            "location": "Presidio",
            "start": to_minutes(11, 0),
            "end": to_minutes(21, 0),
            "min_duration": 90,
        },
        {
            "name": "Margaret",
            "location": "Chinatown",
            "start": to_minutes(9, 15),
            "end": to_minutes(18, 45),
            "min_duration": 90,
        },
        {
            "name": "Nancy",
            "location": "Pacific Heights",
            "start": to_minutes(14, 15),
            "end": to_minutes(17, 0),
            "min_duration": 15,
        },
        {
            "name": "Helen",
            "location": "Richmond District",
            "start": to_minutes(19, 45),
            "end": to_minutes(22, 0),
            "min_duration": 60,
        },
        {
            "name": "Rebecca",
            "location": "Fisherman's Wharf",
            "start": to_minutes(21, 15),
            "end": to_minutes(22, 15),
            "min_duration": 60,
        },
        {
            "name": "Kimberly",
            "location": "Golden Gate Park",
            "start": to_minutes(13, 0),
            "end": to_minutes(16, 30),
            "min_duration": 120,
        },
        {
            "name": "Kenneth",
            "location": "Bayview",
            "start": to_minutes(14, 30),
            "end": to_minutes(18, 0),
            "min_duration": 60,
        },
    ]

    # Compute optimal schedule
    best = search_best(start_location, start_time, people, travel)

    # Convert to requested JSON structure with time strings
    itinerary = []
    for entry in best["path"]:
        itinerary.append({
            "action": "meet",
            "location": entry["location"],
            "person": entry["person"],
            "start_time": time_str(entry["start_time"]),
            "end_time": time_str(entry["end_time"]),
        })

    result = {"itinerary": itinerary}
    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    main()