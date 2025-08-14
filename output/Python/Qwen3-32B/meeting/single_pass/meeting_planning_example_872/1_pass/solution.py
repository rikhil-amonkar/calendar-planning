import itertools
import json

def time_str_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time_str(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

travel_times = {
    "Presidio": {
        "Haight-Ashbury": 15,
        "Nob Hill": 18,
        "Russian Hill": 14,
        "North Beach": 18,
        "Chinatown": 21,
        "Union Square": 22,
        "Embarcadero": 20,
        "Financial District": 23,
        "Marina District": 11,
    },
    "Haight-Ashbury": {
        "Presidio": 15,
        "Nob Hill": 15,
        "Russian Hill": 17,
        "North Beach": 19,
        "Chinatown": 19,
        "Union Square": 19,
        "Embarcadero": 20,
        "Financial District": 21,
        "Marina District": 17,
    },
    "Nob Hill": {
        "Presidio": 17,
        "Haight-Ashbury": 13,
        "Russian Hill": 5,
        "North Beach": 8,
        "Chinatown": 6,
        "Union Square": 7,
        "Embarcadero": 9,
        "Financial District": 9,
        "Marina District": 11,
    },
    "Russian Hill": {
        "Presidio": 14,
        "Haight-Ashbury": 17,
        "Nob Hill": 5,
        "North Beach": 5,
        "Chinatown": 9,
        "Union Square": 10,
        "Embarcadero": 8,
        "Financial District": 11,
        "Marina District": 7,
    },
    "North Beach": {
        "Presidio": 17,
        "Haight-Ashbury": 18,
        "Nob Hill": 7,
        "Russian Hill": 4,
        "Chinatown": 6,
        "Union Square": 7,
        "Embarcadero": 6,
        "Financial District": 8,
        "Marina District": 9,
    },
    "Chinatown": {
        "Presidio": 19,
        "Haight-Ashbury": 19,
        "Nob Hill": 9,
        "Russian Hill": 7,
        "North Beach": 3,
        "Union Square": 7,
        "Embarcadero": 5,
        "Financial District": 5,
        "Marina District": 12,
    },
    "Union Square": {
        "Presidio": 24,
        "Haight-Ashbury": 18,
        "Nob Hill": 9,
        "Russian Hill": 13,
        "North Beach": 10,
        "Chinatown": 7,
        "Embarcadero": 11,
        "Financial District": 9,
        "Marina District": 18,
    },
    "Embarcadero": {
        "Presidio": 20,
        "Haight-Ashbury": 21,
        "Nob Hill": 10,
        "Russian Hill": 8,
        "North Beach": 5,
        "Chinatown": 7,
        "Union Square": 10,
        "Financial District": 5,
        "Marina District": 12,
    },
    "Financial District": {
        "Presidio": 22,
        "Haight-Ashbury": 19,
        "Nob Hill": 8,
        "Russian Hill": 11,
        "North Beach": 7,
        "Chinatown": 5,
        "Union Square": 9,
        "Embarcadero": 4,
        "Marina District": 15,
    },
    "Marina District": {
        "Presidio": 10,
        "Haight-Ashbury": 16,
        "Nob Hill": 12,
        "Russian Hill": 8,
        "North Beach": 11,
        "Chinatown": 15,
        "Union Square": 16,
        "Embarcadero": 14,
        "Financial District": 17,
    },
}

friends = [
    {"name": "Jason", "location": "Chinatown", "available_start": "8:15", "available_end": "11:45", "required_duration": 75},
    {"name": "Kenneth", "location": "North Beach", "available_start": "9:45", "available_end": "21:00", "required_duration": 30},
    {"name": "Kimberly", "location": "Embarcadero", "available_start": "9:45", "available_end": "19:30", "required_duration": 75},
    {"name": "Steven", "location": "Financial District", "available_start": "7:15", "available_end": "21:15", "required_duration": 60},
    {"name": "Mark", "location": "Marina District", "available_start": "10:15", "available_end": "13:00", "required_duration": 75},
    {"name": "Karen", "location": "Haight-Ashbury", "available_start": "21:00", "available_end": "21:45", "required_duration": 45},
    {"name": "Jessica", "location": "Nob Hill", "available_start": "13:45", "available_end": "21:00", "required_duration": 90},
    {"name": "Brian", "location": "Russian Hill", "available_start": "15:30", "available_end": "21:45", "required_duration": 60},
    {"name": "Stephanie", "location": "Union Square", "available_start": "14:45", "available_end": "18:45", "required_duration": 105},
]

best_itinerary = None

for k in range(len(friends), 0, -1):
    for perm in itertools.permutations(friends, k):
        current_time = time_str_to_minutes("9:00")
        current_location = "Presidio"
        itinerary = []
        valid = True
        for friend in perm:
            loc = friend["location"]
            start_time_minutes = time_str_to_minutes(friend["available_start"])
            end_time_minutes = time_str_to_minutes(friend["available_end"])
            required = friend["required_duration"]

            # Calculate travel time
            travel_time = travel_times[current_location][loc]
            arrival_time = current_time + travel_time

            # Check if meeting is possible
            earliest_start = max(arrival_time, start_time_minutes)
            if earliest_start + required > end_time_minutes:
                valid = False
                break

            # Schedule meeting
            current_time = earliest_start + required
            current_location = loc
            itinerary.append({
                "action": "meet",
                "location": loc,
                "person": friend["name"],
                "start_time": minutes_to_time_str(earliest_start),
                "end_time": minutes_to_time_str(current_time)
            })

        if valid:
            best_itinerary = itinerary
            # Output and exit immediately
            print(json.dumps({"itinerary": best_itinerary}))
            exit()

# If no valid itinerary found (unlikely)
print(json.dumps({"itinerary": []}))