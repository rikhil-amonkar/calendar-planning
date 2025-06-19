import json

def minutes_to_time(total_minutes):
    hours = total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours}:{minutes:02d}"

travel_matrix = {
    "Russian Hill": {
        "Sunset District": 23, "Union Square": 10, "Nob Hill": 5, "Marina District": 7,
        "Richmond District": 14, "Financial District": 11, "Embarcadero": 8, "The Castro": 21,
        "Alamo Square": 15, "Presidio": 14
    },
    "Sunset District": {
        "Russian Hill": 24, "Union Square": 30, "Nob Hill": 27, "Marina District": 21,
        "Richmond District": 12, "Financial District": 30, "Embarcadero": 30, "The Castro": 17,
        "Alamo Square": 17, "Presidio": 16
    },
    "Union Square": {
        "Russian Hill": 13, "Sunset District": 27, "Nob Hill": 9, "Marina District": 18,
        "Richmond District": 20, "Financial District": 9, "Embarcadero": 11, "The Castro": 17,
        "Alamo Square": 15, "Presidio": 24
    },
    "Nob Hill": {
        "Russian Hill": 5, "Sunset District": 24, "Union Square": 7, "Marina District": 11,
        "Richmond District": 14, "Financial District": 9, "Embarcadero": 9, "The Castro": 17,
        "Alamo Square": 11, "Presidio": 17
    },
    "Marina District": {
        "Russian Hill": 8, "Sunset District": 19, "Union Square": 16, "Nob Hill": 12,
        "Richmond District": 11, "Financial District": 17, "Embarcadero": 14, "The Castro": 22,
        "Alamo Square": 15, "Presidio": 10
    },
    "Richmond District": {
        "Russian Hill": 13, "Sunset District": 11, "Union Square": 21, "Nob Hill": 17,
        "Marina District": 9, "Financial District": 22, "Embarcadero": 19, "The Castro": 16,
        "Alamo Square": 13, "Presidio": 7
    },
    "Financial District": {
        "Russian Hill": 11, "Sunset District": 30, "Union Square": 9, "Nob Hill": 8,
        "Marina District": 15, "Richmond District": 21, "Embarcadero": 4, "The Castro": 20,
        "Alamo Square": 17, "Presidio": 22
    },
    "Embarcadero": {
        "Russian Hill": 8, "Sunset District": 30, "Union Square": 10, "Nob Hill": 10,
        "Marina District": 12, "Richmond District": 21, "Financial District": 5, "The Castro": 25,
        "Alamo Square": 19, "Presidio": 20
    },
    "The Castro": {
        "Russian Hill": 18, "Sunset District": 17, "Union Square": 19, "Nob Hill": 16,
        "Marina District": 21, "Richmond District": 16, "Financial District": 21, "Embarcadero": 22,
        "Alamo Square": 8, "Presidio": 20
    },
    "Alamo Square": {
        "Russian Hill": 13, "Sunset District": 16, "Union Square": 14, "Nob Hill": 11,
        "Marina District": 15, "Richmond District": 11, "Financial District": 17, "Embarcadero": 16,
        "The Castro": 8, "Presidio": 17
    },
    "Presidio": {
        "Russian Hill": 14, "Sunset District": 15, "Union Square": 22, "Nob Hill": 18,
        "Marina District": 11, "Richmond District": 7, "Financial District": 23, "Embarcadero": 20,
        "The Castro": 21, "Alamo Square": 19
    }
}

meetings = [
    ("William", "Presidio", 7*60, 12*60+45, 60),
    ("Kimberly", "Alamo Square", 9*60, 14*60+30, 105),
    ("George", "The Castro", 14*60+15, 19*60, 105),
    ("Patricia", "Nob Hill", 15*60, 19*60+15, 120),
    ("Charles", "Richmond District", 17*60+15, 21*60, 15),
    ("Ronald", "Embarcadero", 18*60+15, 20*60+45, 30),
    ("David", "Sunset District", 9*60+15, 22*60, 15),
    ("Kenneth", "Union Square", 21*60+15, 21*60+45, 15)
]

current_time = 540
current_location = "Russian Hill"
itinerary = []
unscheduled = meetings[:]

threshold = 18 * 60  # 18:00 in minutes

while unscheduled:
    candidates = []
    for idx, m in enumerate(unscheduled):
        person, location, avail_start, avail_end, min_duration = m
        travel_time = travel_matrix[current_location][location]
        arrival_time = current_time + travel_time
        start_time = max(arrival_time, avail_start)
        end_time = start_time + min_duration
        if end_time <= avail_end:
            if avail_end < threshold:
                sort_key = (0, avail_end, end_time)
            else:
                sort_key = (1, avail_start, end_time)
            candidates.append((sort_key, end_time, start_time, idx, m, location))
    if not candidates:
        break
    candidates.sort(key=lambda x: x[0])
    best_candidate = candidates[0]
    end_time_val = best_candidate[1]
    start_time_val = best_candidate[2]
    idx_val = best_candidate[3]
    meeting_val = best_candidate[4]
    location_val = best_candidate[5]
    person, _, _, _, _ = meeting_val
    itinerary.append({
        "action": "meet",
        "location": location_val,
        "person": person,
        "start_time": minutes_to_time(start_time_val),
        "end_time": minutes_to_time(end_time_val)
    })
    current_time = end_time_val
    current_location = location_val
    unscheduled.pop(idx_val)

output = {"itinerary": itinerary}
print(json.dumps(output))