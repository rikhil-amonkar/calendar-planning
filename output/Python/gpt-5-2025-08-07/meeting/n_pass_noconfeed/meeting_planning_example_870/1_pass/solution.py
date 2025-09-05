import json
from itertools import permutations

def to_minutes(hm):
    h, m = map(int, hm.split(':'))
    return h * 60 + m

def minutes_to_str(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# Travel times in minutes (directed)
travel = {
    "Pacific Heights": {
        "Marina District": 6,
        "The Castro": 16,
        "Richmond District": 12,
        "Alamo Square": 10,
        "Financial District": 13,
        "Presidio": 11,
        "Mission District": 15,
        "Nob Hill": 8,
        "Russian Hill": 7
    },
    "Marina District": {
        "Pacific Heights": 7,
        "The Castro": 22,
        "Richmond District": 11,
        "Alamo Square": 15,
        "Financial District": 17,
        "Presidio": 10,
        "Mission District": 20,
        "Nob Hill": 12,
        "Russian Hill": 8
    },
    "The Castro": {
        "Pacific Heights": 16,
        "Marina District": 21,
        "Richmond District": 16,
        "Alamo Square": 8,
        "Financial District": 21,
        "Presidio": 20,
        "Mission District": 7,
        "Nob Hill": 16,
        "Russian Hill": 18
    },
    "Richmond District": {
        "Pacific Heights": 10,
        "Marina District": 9,
        "The Castro": 16,
        "Alamo Square": 13,
        "Financial District": 22,
        "Presidio": 7,
        "Mission District": 20,
        "Nob Hill": 17,
        "Russian Hill": 13
    },
    "Alamo Square": {
        "Pacific Heights": 10,
        "Marina District": 15,
        "The Castro": 8,
        "Richmond District": 11,
        "Financial District": 17,
        "Presidio": 17,
        "Mission District": 10,
        "Nob Hill": 11,
        "Russian Hill": 13
    },
    "Financial District": {
        "Pacific Heights": 13,
        "Marina District": 15,
        "The Castro": 20,
        "Richmond District": 21,
        "Alamo Square": 17,
        "Presidio": 22,
        "Mission District": 17,
        "Nob Hill": 8,
        "Russian Hill": 11
    },
    "Presidio": {
        "Pacific Heights": 11,
        "Marina District": 11,
        "The Castro": 21,
        "Richmond District": 7,
        "Alamo Square": 19,
        "Financial District": 23,
        "Mission District": 26,
        "Nob Hill": 18,
        "Russian Hill": 14
    },
    "Mission District": {
        "Pacific Heights": 16,
        "Marina District": 19,
        "The Castro": 7,
        "Richmond District": 20,
        "Alamo Square": 11,
        "Financial District": 15,
        "Presidio": 25,
        "Nob Hill": 12,
        "Russian Hill": 15
    },
    "Nob Hill": {
        "Pacific Heights": 8,
        "Marina District": 11,
        "The Castro": 17,
        "Richmond District": 14,
        "Alamo Square": 11,
        "Financial District": 9,
        "Presidio": 17,
        "Mission District": 13,
        "Russian Hill": 5
    },
    "Russian Hill": {
        "Pacific Heights": 7,
        "Marina District": 7,
        "The Castro": 21,
        "Richmond District": 14,
        "Alamo Square": 15,
        "Financial District": 11,
        "Presidio": 14,
        "Mission District": 16,
        "Nob Hill": 5
    }
}

# Friends constraints: location, availability window [start, end], minimum meeting duration
friends = {
    "Linda":    {"location": "Marina District",   "start": to_minutes("18:00"), "end": to_minutes("22:00"), "min": 30},
    "Kenneth":  {"location": "The Castro",        "start": to_minutes("14:45"), "end": to_minutes("16:15"), "min": 30},
    "Kimberly": {"location": "Richmond District", "start": to_minutes("14:15"), "end": to_minutes("22:00"), "min": 30},
    "Paul":     {"location": "Alamo Square",      "start": to_minutes("21:00"), "end": to_minutes("21:30"), "min": 15},
    "Carol":    {"location": "Financial District","start": to_minutes("10:15"), "end": to_minutes("12:00"), "min": 60},
    "Brian":    {"location": "Presidio",          "start": to_minutes("10:00"), "end": to_minutes("21:30"), "min": 75},
    "Laura":    {"location": "Mission District",  "start": to_minutes("16:15"), "end": to_minutes("20:30"), "min": 30},
    "Sandra":   {"location": "Nob Hill",          "start": to_minutes("9:15"),  "end": to_minutes("18:30"), "min": 60},
    "Karen":    {"location": "Russian Hill",      "start": to_minutes("18:30"), "end": to_minutes("22:00"), "min": 75},
}

start_location = "Pacific Heights"
start_time = to_minutes("9:00")

# Backtracking search to maximize number of meetings; tie-break by earliest finish, then minimal total travel+wait
best_solution = {
    "count": 0,
    "finish_time": float('inf'),
    "travel_wait": float('inf'),
    "itinerary": []
}

def backtrack(current_loc, current_time, remaining, itinerary, total_travel, total_wait):
    global best_solution

    # Update best solution
    if len(itinerary) > best_solution["count"] or \
       (len(itinerary) == best_solution["count"] and (current_time < best_solution["finish_time"] or \
        (current_time == best_solution["finish_time"] and (total_travel + total_wait) < best_solution["travel_wait"]))):
        best_solution = {
            "count": len(itinerary),
            "finish_time": current_time,
            "travel_wait": total_travel + total_wait,
            "itinerary": itinerary.copy()
        }

    # Try to meet each remaining friend
    for person in list(remaining):
        info = friends[person]
        loc_to = info["location"]
        travel_time = travel[current_loc][loc_to]
        arrival = current_time + travel_time
        # Earliest feasible start
        start = max(arrival, info["start"])
        end = start + info["min"]
        if end <= info["end"]:
            wait = max(0, info["start"] - arrival)
            itinerary.append({
                "action": "meet",
                "location": loc_to,
                "person": person,
                "start_time": minutes_to_str(start),
                "end_time": minutes_to_str(end)
            })
            remaining.remove(person)
            backtrack(loc_to, end, remaining, itinerary, total_travel + travel_time, total_wait + wait)
            # backtrack
            remaining.add(person)
            itinerary.pop()

# Prepare search
remaining_set = set(friends.keys())
backtrack(start_location, start_time, remaining_set, [], 0, 0)

# Output JSON
output = {
    "itinerary": best_solution["itinerary"]
}
print(json.dumps(output, ensure_ascii=False))