# SOLUTION:
import itertools
import json

def time_to_minutes(t):
    # t like '9:00' or '13:30' (24h)
    h, m = map(int, t.split(':'))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Travel times (directed, in minutes)
dist = {
    "Presidio": {
        "Pacific Heights": 11,
        "Golden Gate Park": 12,
        "Fisherman's Wharf": 19,
        "Marina District": 11,
        "Alamo Square": 19,
        "Sunset District": 15,
        "Nob Hill": 18,
        "North Beach": 18
    },
    "Pacific Heights": {
        "Presidio": 11,
        "Golden Gate Park": 15,
        "Fisherman's Wharf": 13,
        "Marina District": 6,
        "Alamo Square": 10,
        "Sunset District": 21,
        "Nob Hill": 8,
        "North Beach": 9
    },
    "Golden Gate Park": {
        "Presidio": 11,
        "Pacific Heights": 16,
        "Fisherman's Wharf": 24,
        "Marina District": 16,
        "Alamo Square": 9,
        "Sunset District": 10,
        "Nob Hill": 20,
        "North Beach": 23
    },
    "Fisherman's Wharf": {
        "Presidio": 17,
        "Pacific Heights": 12,
        "Golden Gate Park": 25,
        "Marina District": 9,
        "Alamo Square": 21,
        "Sunset District": 27,
        "Nob Hill": 11,
        "North Beach": 6
    },
    "Marina District": {
        "Presidio": 10,
        "Pacific Heights": 7,
        "Golden Gate Park": 18,
        "Fisherman's Wharf": 10,
        "Alamo Square": 15,
        "Sunset District": 19,
        "Nob Hill": 12,
        "North Beach": 11
    },
    "Alamo Square": {
        "Presidio": 17,
        "Pacific Heights": 10,
        "Golden Gate Park": 9,
        "Fisherman's Wharf": 19,
        "Marina District": 15,
        "Sunset District": 16,
        "Nob Hill": 11,
        "North Beach": 15
    },
    "Sunset District": {
        "Presidio": 16,
        "Pacific Heights": 21,
        "Golden Gate Park": 11,
        "Fisherman's Wharf": 29,
        "Marina District": 21,
        "Alamo Square": 17,
        "Nob Hill": 27,
        "North Beach": 28
    },
    "Nob Hill": {
        "Presidio": 17,
        "Pacific Heights": 8,
        "Golden Gate Park": 17,
        "Fisherman's Wharf": 10,
        "Marina District": 11,
        "Alamo Square": 11,
        "Sunset District": 24,
        "North Beach": 8
    },
    "North Beach": {
        "Presidio": 17,
        "Pacific Heights": 8,
        "Golden Gate Park": 22,
        "Fisherman's Wharf": 5,
        "Marina District": 9,
        "Alamo Square": 16,
        "Sunset District": 27,
        "Nob Hill": 7
    }
}

# Input constraints
arrival_location = "Presidio"
arrival_time_str = "9:00"
arrival_time = time_to_minutes(arrival_time_str)

people = {
    "Kevin": {
        "location": "Pacific Heights",
        "window_start": time_to_minutes("7:15"),
        "window_end": time_to_minutes("8:45"),
        "min_duration": 90
    },
    "Michelle": {
        "location": "Golden Gate Park",
        "window_start": time_to_minutes("20:00"),
        "window_end": time_to_minutes("21:00"),
        "min_duration": 15
    },
    "Emily": {
        "location": "Fisherman's Wharf",
        "window_start": time_to_minutes("16:15"),
        "window_end": time_to_minutes("19:00"),
        "min_duration": 30
    },
    "Mark": {
        "location": "Marina District",
        "window_start": time_to_minutes("18:15"),
        "window_end": time_to_minutes("19:45"),
        "min_duration": 75
    },
    "Barbara": {
        "location": "Alamo Square",
        "window_start": time_to_minutes("17:00"),
        "window_end": time_to_minutes("19:00"),
        "min_duration": 120
    },
    "Laura": {
        "location": "Sunset District",
        "window_start": time_to_minutes("19:00"),
        "window_end": time_to_minutes("21:15"),
        "min_duration": 75
    },
    "Mary": {
        "location": "Nob Hill",
        "window_start": time_to_minutes("17:30"),
        "window_end": time_to_minutes("19:00"),
        "min_duration": 45
    },
    "Helen": {
        "location": "North Beach",
        "window_start": time_to_minutes("11:00"),
        "window_end": time_to_minutes("12:15"),
        "min_duration": 45
    }
}

names = list(people.keys())

def simulate_order(order):
    current_time = arrival_time
    current_loc = arrival_location
    itinerary = []
    total_travel = 0
    total_meeting = 0

    for name in order:
        person = people[name]
        loc = person["location"]
        if current_loc not in dist or loc not in dist[current_loc]:
            # If travel time unknown, skip
            continue
        travel = dist[current_loc][loc]
        arrive = current_time + travel
        start = max(arrive, person["window_start"])
        end = start + person["min_duration"]
        if end <= person["window_end"]:
            # feasible
            itinerary.append({
                "action": "meet",
                "location": loc,
                "person": name,
                "start_time": minutes_to_time(start),
                "end_time": minutes_to_time(end)
            })
            current_time = end
            current_loc = loc
            total_travel += travel
            total_meeting += person["min_duration"]
        else:
            # skip this person
            continue

    finish_time = current_time
    return itinerary, total_meeting, total_travel, finish_time

best = {
    "itinerary": [],
    "count": -1,
    "total_meeting": -1,
    "total_travel": float('inf'),
    "finish_time": float('inf')
}

# Explore all permutations
for order in itertools.permutations(names):
    itinerary, t_meet, t_travel, finish = simulate_order(order)
    count = len(itinerary)

    # Primary: maximize count
    better = False
    if count > best["count"]:
        better = True
    elif count == best["count"]:
        # Secondary: maximize total meeting minutes
        if t_meet > best["total_meeting"]:
            better = True
        elif t_meet == best["total_meeting"]:
            # Tertiary: minimize total travel time
            if t_travel < best["total_travel"]:
                better = True
            elif t_travel == best["total_travel"]:
                # Quaternary: finish earlier
                if finish < best["finish_time"]:
                    better = True

    if better:
        best = {
            "itinerary": itinerary,
            "count": count,
            "total_meeting": t_meet,
            "total_travel": t_travel,
            "finish_time": finish
        }

# Prepare output JSON
output = {
    "itinerary": best["itinerary"]
}

print("SOLUTION:")
print(json.dumps(output, indent=2))