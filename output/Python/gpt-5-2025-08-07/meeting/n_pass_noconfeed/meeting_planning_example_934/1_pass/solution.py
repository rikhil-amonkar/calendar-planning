# SOLUTION:
import json
from copy import deepcopy

def time_to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

def build_travel_times():
    t = {}
    locations = [
        "Nob Hill", "Embarcadero", "The Castro", "Haight-Ashbury",
        "Union Square", "North Beach", "Pacific Heights", "Chinatown",
        "Golden Gate Park", "Marina District", "Russian Hill"
    ]
    for loc in locations:
        t[loc] = {}
    # Populate directed travel times (in minutes)
    t["Nob Hill"]["Embarcadero"] = 9
    t["Nob Hill"]["The Castro"] = 17
    t["Nob Hill"]["Haight-Ashbury"] = 13
    t["Nob Hill"]["Union Square"] = 7
    t["Nob Hill"]["North Beach"] = 8
    t["Nob Hill"]["Pacific Heights"] = 8
    t["Nob Hill"]["Chinatown"] = 6
    t["Nob Hill"]["Golden Gate Park"] = 17
    t["Nob Hill"]["Marina District"] = 11
    t["Nob Hill"]["Russian Hill"] = 5

    t["Embarcadero"]["Nob Hill"] = 10
    t["Embarcadero"]["The Castro"] = 25
    t["Embarcadero"]["Haight-Ashbury"] = 21
    t["Embarcadero"]["Union Square"] = 10
    t["Embarcadero"]["North Beach"] = 5
    t["Embarcadero"]["Pacific Heights"] = 11
    t["Embarcadero"]["Chinatown"] = 7
    t["Embarcadero"]["Golden Gate Park"] = 25
    t["Embarcadero"]["Marina District"] = 12
    t["Embarcadero"]["Russian Hill"] = 8

    t["The Castro"]["Nob Hill"] = 16
    t["The Castro"]["Embarcadero"] = 22
    t["The Castro"]["Haight-Ashbury"] = 6
    t["The Castro"]["Union Square"] = 19
    t["The Castro"]["North Beach"] = 20
    t["The Castro"]["Pacific Heights"] = 16
    t["The Castro"]["Chinatown"] = 22
    t["The Castro"]["Golden Gate Park"] = 11
    t["The Castro"]["Marina District"] = 21
    t["The Castro"]["Russian Hill"] = 18

    t["Haight-Ashbury"]["Nob Hill"] = 15
    t["Haight-Ashbury"]["Embarcadero"] = 20
    t["Haight-Ashbury"]["The Castro"] = 6
    t["Haight-Ashbury"]["Union Square"] = 19
    t["Haight-Ashbury"]["North Beach"] = 19
    t["Haight-Ashbury"]["Pacific Heights"] = 12
    t["Haight-Ashbury"]["Chinatown"] = 19
    t["Haight-Ashbury"]["Golden Gate Park"] = 7
    t["Haight-Ashbury"]["Marina District"] = 17
    t["Haight-Ashbury"]["Russian Hill"] = 17

    t["Union Square"]["Nob Hill"] = 9
    t["Union Square"]["Embarcadero"] = 11
    t["Union Square"]["The Castro"] = 17
    t["Union Square"]["Haight-Ashbury"] = 18
    t["Union Square"]["North Beach"] = 10
    t["Union Square"]["Pacific Heights"] = 15
    t["Union Square"]["Chinatown"] = 7
    t["Union Square"]["Golden Gate Park"] = 22
    t["Union Square"]["Marina District"] = 18
    t["Union Square"]["Russian Hill"] = 13

    t["North Beach"]["Nob Hill"] = 7
    t["North Beach"]["Embarcadero"] = 6
    t["North Beach"]["The Castro"] = 23
    t["North Beach"]["Haight-Ashbury"] = 18
    t["North Beach"]["Union Square"] = 7
    t["North Beach"]["Pacific Heights"] = 8
    t["North Beach"]["Chinatown"] = 6
    t["North Beach"]["Golden Gate Park"] = 22
    t["North Beach"]["Marina District"] = 9
    t["North Beach"]["Russian Hill"] = 4

    t["Pacific Heights"]["Nob Hill"] = 8
    t["Pacific Heights"]["Embarcadero"] = 10
    t["Pacific Heights"]["The Castro"] = 16
    t["Pacific Heights"]["Haight-Ashbury"] = 11
    t["Pacific Heights"]["Union Square"] = 12
    t["Pacific Heights"]["North Beach"] = 9
    t["Pacific Heights"]["Chinatown"] = 11
    t["Pacific Heights"]["Golden Gate Park"] = 15
    t["Pacific Heights"]["Marina District"] = 6
    t["Pacific Heights"]["Russian Hill"] = 7

    t["Chinatown"]["Nob Hill"] = 9
    t["Chinatown"]["Embarcadero"] = 5
    t["Chinatown"]["The Castro"] = 22
    t["Chinatown"]["Haight-Ashbury"] = 19
    t["Chinatown"]["Union Square"] = 7
    t["Chinatown"]["North Beach"] = 3
    t["Chinatown"]["Pacific Heights"] = 10
    t["Chinatown"]["Golden Gate Park"] = 23
    t["Chinatown"]["Marina District"] = 12
    t["Chinatown"]["Russian Hill"] = 7

    t["Golden Gate Park"]["Nob Hill"] = 20
    t["Golden Gate Park"]["Embarcadero"] = 25
    t["Golden Gate Park"]["The Castro"] = 13
    t["Golden Gate Park"]["Haight-Ashbury"] = 7
    t["Golden Gate Park"]["Union Square"] = 22
    t["Golden Gate Park"]["North Beach"] = 23
    t["Golden Gate Park"]["Pacific Heights"] = 16
    t["Golden Gate Park"]["Chinatown"] = 23
    t["Golden Gate Park"]["Marina District"] = 16
    t["Golden Gate Park"]["Russian Hill"] = 19

    t["Marina District"]["Nob Hill"] = 12
    t["Marina District"]["Embarcadero"] = 14
    t["Marina District"]["The Castro"] = 22
    t["Marina District"]["Haight-Ashbury"] = 16
    t["Marina District"]["Union Square"] = 16
    t["Marina District"]["North Beach"] = 11
    t["Marina District"]["Pacific Heights"] = 7
    t["Marina District"]["Chinatown"] = 15
    t["Marina District"]["Golden Gate Park"] = 18
    t["Marina District"]["Russian Hill"] = 8

    t["Russian Hill"]["Nob Hill"] = 5
    t["Russian Hill"]["Embarcadero"] = 8
    t["Russian Hill"]["The Castro"] = 21
    t["Russian Hill"]["Haight-Ashbury"] = 17
    t["Russian Hill"]["Union Square"] = 10
    t["Russian Hill"]["North Beach"] = 5
    t["Russian Hill"]["Pacific Heights"] = 7
    t["Russian Hill"]["Chinatown"] = 9
    t["Russian Hill"]["Golden Gate Park"] = 21
    t["Russian Hill"]["Marina District"] = 7

    return t

def build_people():
    # Define availability windows and minimum durations (minutes)
    people = {
        "Mary": {
            "location": "Embarcadero",
            "start": time_to_minutes("20:00"),
            "end": time_to_minutes("21:15"),
            "dur": 75
        },
        "Kenneth": {
            "location": "The Castro",
            "start": time_to_minutes("11:15"),
            "end": time_to_minutes("19:15"),
            "dur": 30
        },
        "Joseph": {
            "location": "Haight-Ashbury",
            "start": time_to_minutes("20:00"),
            "end": time_to_minutes("22:00"),
            "dur": 120
        },
        "Sarah": {
            "location": "Union Square",
            "start": time_to_minutes("11:45"),
            "end": time_to_minutes("14:30"),
            "dur": 90
        },
        "Thomas": {
            "location": "North Beach",
            "start": time_to_minutes("19:15"),
            "end": time_to_minutes("19:45"),
            "dur": 15
        },
        "Daniel": {
            "location": "Pacific Heights",
            "start": time_to_minutes("13:45"),
            "end": time_to_minutes("20:30"),
            "dur": 15
        },
        "Richard": {
            "location": "Chinatown",
            "start": time_to_minutes("8:00"),
            "end": time_to_minutes("18:45"),
            "dur": 30
        },
        "Mark": {
            "location": "Golden Gate Park",
            "start": time_to_minutes("17:30"),
            "end": time_to_minutes("21:30"),
            "dur": 120
        },
        "David": {
            "location": "Marina District",
            "start": time_to_minutes("20:00"),
            "end": time_to_minutes("21:00"),
            "dur": 60
        },
        "Karen": {
            "location": "Russian Hill",
            "start": time_to_minutes("13:15"),
            "end": time_to_minutes("18:30"),
            "dur": 120
        }
    }
    return people

def schedule_next(travel, current_loc, current_time, person):
    loc = person["location"]
    travel_time = travel[current_loc][loc]
    arrival = current_time + travel_time
    start = max(arrival, person["start"])
    end = start + person["dur"]
    if end <= person["end"]:
        return start, end
    else:
        return None

def compute_optimal_schedule():
    travel = build_travel_times()
    people = build_people()

    start_location = "Nob Hill"
    start_time = time_to_minutes("9:00")

    names = list(people.keys())

    best = {
        "count": 0,
        "total_meet_minutes": 0,
        "finish_time": float('inf'),
        "itinerary": []
    }

    # For tie-breaking consistency, order candidates by earlier latest start then earlier end
    def candidate_sort_key(name):
        p = people[name]
        latest_start = p["end"] - p["dur"]
        return (latest_start, p["end"])

    # DFS with pruning
    def dfs(current_loc, current_time, remaining_names, itinerary, met_count, meeting_minutes):
        # Update best
        if (met_count > best["count"] or
            (met_count == best["count"] and meeting_minutes > best["total_meet_minutes"]) or
            (met_count == best["count"] and meeting_minutes == best["total_meet_minutes"] and (itinerary[-1]["end"] if itinerary else current_time) < best["finish_time"])):
            best["count"] = met_count
            best["total_meet_minutes"] = meeting_minutes
            best["finish_time"] = itinerary[-1]["end"] if itinerary else current_time
            best["itinerary"] = deepcopy(itinerary)

        # Upper bound pruning
        if met_count + len(remaining_names) <= best["count"]:
            return

        # Sort candidates with heuristic
        sorted_names = sorted(remaining_names, key=candidate_sort_key)

        for name in sorted_names:
            p = people[name]
            # Quick feasibility: can we at least reach before latest start?
            latest_start = p["end"] - p["dur"]
            # Compute minimum arrival time from current state
            min_arrival = current_time + travel[current_loc][p["location"]]
            if min_arrival > latest_start:
                continue  # impossible to catch
            sch = schedule_next(travel, current_loc, current_time, p)
            if not sch:
                continue
            start, end = sch
            new_it = itinerary + [{
                "action": "meet",
                "location": p["location"],
                "person": name,
                "start": start,
                "end": end
            }]
            new_remaining = [n for n in remaining_names if n != name]
            dfs(p["location"], end, new_remaining, new_it, met_count + 1, meeting_minutes + p["dur"])

    dfs(start_location, start_time, names, [], 0, 0)

    # Format output
    out_itinerary = []
    # Sort itinerary by start time to ensure chronological order (already chronological by construction)
    best_it = sorted(best["itinerary"], key=lambda x: x["start"])
    for item in best_it:
        out_itinerary.append({
            "action": "meet",
            "location": item["location"],
            "person": item["person"],
            "start_time": minutes_to_time(item["start"]),
            "end_time": minutes_to_time(item["end"])
        })

    return {"itinerary": out_itinerary}

if __name__ == "__main__":
    result = compute_optimal_schedule()
    print(json.dumps(result, ensure_ascii=False))