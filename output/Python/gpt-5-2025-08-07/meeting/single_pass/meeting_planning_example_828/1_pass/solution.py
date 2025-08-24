import json

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Travel times in minutes (directed)
travel = {
    "Marina District": {
        "Richmond District": 11,
        "Union Square": 16,
        "Nob Hill": 12,
        "Fisherman's Wharf": 10,
        "Golden Gate Park": 18,
        "Embarcadero": 14,
        "Financial District": 17,
        "North Beach": 11,
        "Presidio": 10
    },
    "Richmond District": {
        "Marina District": 9,
        "Union Square": 21,
        "Nob Hill": 17,
        "Fisherman's Wharf": 18,
        "Golden Gate Park": 9,
        "Embarcadero": 19,
        "Financial District": 22,
        "North Beach": 17,
        "Presidio": 7
    },
    "Union Square": {
        "Marina District": 18,
        "Richmond District": 20,
        "Nob Hill": 9,
        "Fisherman's Wharf": 15,
        "Golden Gate Park": 22,
        "Embarcadero": 11,
        "Financial District": 9,
        "North Beach": 10,
        "Presidio": 24
    },
    "Nob Hill": {
        "Marina District": 11,
        "Richmond District": 14,
        "Union Square": 7,
        "Fisherman's Wharf": 10,
        "Golden Gate Park": 17,
        "Embarcadero": 9,
        "Financial District": 9,
        "North Beach": 8,
        "Presidio": 17
    },
    "Fisherman's Wharf": {
        "Marina District": 9,
        "Richmond District": 18,
        "Union Square": 13,
        "Nob Hill": 11,
        "Golden Gate Park": 25,
        "Embarcadero": 8,
        "Financial District": 11,
        "North Beach": 6,
        "Presidio": 17
    },
    "Golden Gate Park": {
        "Marina District": 16,
        "Richmond District": 7,
        "Union Square": 22,
        "Nob Hill": 20,
        "Fisherman's Wharf": 24,
        "Embarcadero": 25,
        "Financial District": 26,
        "North Beach": 23,
        "Presidio": 11
    },
    "Embarcadero": {
        "Marina District": 12,
        "Richmond District": 21,
        "Union Square": 10,
        "Nob Hill": 10,
        "Fisherman's Wharf": 6,
        "Golden Gate Park": 25,
        "Financial District": 5,
        "North Beach": 5,
        "Presidio": 20
    },
    "Financial District": {
        "Marina District": 15,
        "Richmond District": 21,
        "Union Square": 9,
        "Nob Hill": 8,
        "Fisherman's Wharf": 10,
        "Golden Gate Park": 23,
        "Embarcadero": 4,
        "North Beach": 7,
        "Presidio": 22
    },
    "North Beach": {
        "Marina District": 9,
        "Richmond District": 18,
        "Union Square": 7,
        "Nob Hill": 7,
        "Fisherman's Wharf": 5,
        "Golden Gate Park": 22,
        "Embarcadero": 6,
        "Financial District": 8,
        "Presidio": 17
    },
    "Presidio": {
        "Marina District": 11,
        "Richmond District": 7,
        "Union Square": 22,
        "Nob Hill": 18,
        "Fisherman's Wharf": 19,
        "Golden Gate Park": 12,
        "Embarcadero": 20,
        "Financial District": 23,
        "North Beach": 18
    }
}

# Ensure zero travel time for same-location moves
for a in list(travel.keys()):
    travel[a][a] = 0

# People constraints
people = {
    "Stephanie": {
        "location": "Richmond District",
        "start": 16*60 + 15,  # 16:15
        "end": 21*60 + 30,    # 21:30
        "min": 75
    },
    "William": {
        "location": "Union Square",
        "start": 10*60 + 45,  # 10:45
        "end": 17*60 + 30,    # 17:30
        "min": 45
    },
    "Elizabeth": {
        "location": "Nob Hill",
        "start": 12*60 + 15,  # 12:15
        "end": 15*60 + 0,     # 15:00
        "min": 105
    },
    "Joseph": {
        "location": "Fisherman's Wharf",
        "start": 12*60 + 45,  # 12:45
        "end": 14*60 + 0,     # 14:00
        "min": 75
    },
    "Anthony": {
        "location": "Golden Gate Park",
        "start": 13*60 + 0,   # 13:00
        "end": 20*60 + 30,    # 20:30
        "min": 75
    },
    "Barbara": {
        "location": "Embarcadero",
        "start": 19*60 + 15,  # 19:15
        "end": 20*60 + 30,    # 20:30
        "min": 75
    },
    "Carol": {
        "location": "Financial District",
        "start": 11*60 + 45,  # 11:45
        "end": 16*60 + 15,    # 16:15
        "min": 60
    },
    "Sandra": {
        "location": "North Beach",
        "start": 10*60 + 0,   # 10:00
        "end": 12*60 + 30,    # 12:30
        "min": 15
    },
    "Kenneth": {
        "location": "Presidio",
        "start": 21*60 + 15,  # 21:15
        "end": 22*60 + 15,    # 22:15
        "min": 45
    }
}

# Start state
start_location = "Marina District"
start_time = 9 * 60  # 9:00

names = list(people.keys())

best_solution = {
    "count": 0,
    "total_minutes": 0,
    "total_travel": 10**9,
    "itinerary": []
}

# DFS to explore schedules
def dfs(curr_loc, curr_time, remaining, itinerary, total_minutes, total_travel):
    # Update global best solution
    global best_solution
    count = len(itinerary)
    better = False
    if count > best_solution["count"]:
        better = True
    elif count == best_solution["count"]:
        if total_minutes > best_solution["total_minutes"]:
            better = True
        elif total_minutes == best_solution["total_minutes"]:
            if total_travel < best_solution["total_travel"]:
                better = True
    if better:
        best_solution = {
            "count": count,
            "total_minutes": total_minutes,
            "total_travel": total_travel,
            "itinerary": itinerary[:]
        }

    # Simple upper bound pruning
    if count + len(remaining) <= best_solution["count"]:
        return

    # Try each remaining person next
    # Heuristic order: earlier window end first to reduce branching
    ordered = sorted(remaining, key=lambda n: people[n]["end"])
    for name in ordered:
        p = people[name]
        loc = p["location"]
        # Travel time from current location to person's location
        if curr_loc not in travel or loc not in travel[curr_loc]:
            continue  # if missing, skip (shouldn't happen)
        t_travel = travel[curr_loc][loc]
        arrival = curr_time + t_travel
        start_meet = max(arrival, p["start"])
        end_meet = start_meet + p["min"]
        if end_meet <= p["end"]:
            # feasible
            next_itinerary = itinerary + [{
                "action": "meet",
                "location": loc,
                "person": name,
                "start_time": fmt_time(start_meet),
                "end_time": fmt_time(end_meet)
            }]
            next_remaining = [r for r in remaining if r != name]
            dfs(
                loc,
                end_meet,
                next_remaining,
                next_itinerary,
                total_minutes + p["min"],
                total_travel + t_travel
            )

# Run search
dfs(start_location, start_time, names, [], 0, 0)

# Build output JSON
output = {
    "itinerary": best_solution["itinerary"]
}

print(json.dumps(output, ensure_ascii=False))