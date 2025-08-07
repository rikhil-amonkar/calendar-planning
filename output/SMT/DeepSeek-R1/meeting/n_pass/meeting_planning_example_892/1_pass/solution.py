from z3 import *
import json

def time_to_minutes(time_str):
    parts = time_str.split(':')
    hour = int(parts[0])
    minute = int(parts[1])
    return hour * 60 + minute - 540  # 540 minutes = 9:00 AM

def minutes_to_time(minutes):
    total_minutes = minutes + 540
    hour = total_minutes // 60
    minute = total_minutes % 60
    return f"{int(hour):02d}:{int(minute):02d}"

# Define friends data
friends = [
    ("Charles", "Bayview", 45, "11:30", "14:30"),
    ("Robert", "Sunset District", 30, "16:45", "21:00"),
    ("Karen", "Richmond District", 60, "19:15", "21:30"),
    ("Rebecca", "Nob Hill", 90, "16:15", "20:30"),
    ("Margaret", "Chinatown", 120, "14:15", "19:45"),
    ("Patricia", "Haight-Ashbury", 45, "14:30", "20:30"),
    ("Mark", "North Beach", 105, "14:00", "18:30"),
    ("Melissa", "Russian Hill", 30, "13:00", "19:45"),
    ("Laura", "Embarcadero", 105, "7:45", "13:15")
]

# Precomputed travel times between all pairs of locations
travel_times = [
    ("Marina District", "Bayview", 27),
    ("Marina District", "Sunset District", 19),
    ("Marina District", "Richmond District", 11),
    ("Marina District", "Nob Hill", 12),
    ("Marina District", "Chinatown", 15),
    ("Marina District", "Haight-Ashbury", 16),
    ("Marina District", "North Beach", 11),
    ("Marina District", "Russian Hill", 8),
    ("Marina District", "Embarcadero", 14),
    ("Bayview", "Marina District", 27),
    ("Bayview", "Sunset District", 23),
    ("Bayview", "Richmond District", 25),
    ("Bayview", "Nob Hill", 20),
    ("Bayview", "Chinatown", 19),
    ("Bayview", "Haight-Ashbury", 19),
    ("Bayview", "North Beach", 22),
    ("Bayview", "Russian Hill", 23),
    ("Bayview", "Embarcadero", 19),
    ("Sunset District", "Marina District", 21),
    ("Sunset District", "Bayview", 22),
    ("Sunset District", "Richmond District", 12),
    ("Sunset District", "Nob Hill", 27),
    ("Sunset District", "Chinatown", 30),
    ("Sunset District", "Haight-Ashbury", 15),
    ("Sunset District", "North Beach", 28),
    ("Sunset District", "Russian Hill", 24),
    ("Sunset District", "Embarcadero", 30),
    ("Richmond District", "Marina District", 9),
    ("Richmond District", "Bayview", 27),
    ("Richmond District", "Sunset District", 11),
    ("Richmond District", "Nob Hill", 17),
    ("Richmond District", "Chinatown", 20),
    ("Richmond District", "Haight-Ashbury", 10),
    ("Richmond District", "North Beach", 17),
    ("Richmond District", "Russian Hill", 13),
    ("Richmond District", "Embarcadero", 19),
    ("Nob Hill", "Marina District", 11),
    ("Nob Hill", "Bayview", 19),
    ("Nob Hill", "Sunset District", 24),
    ("Nob Hill", "Richmond District", 14),
    ("Nob Hill", "Chinatown", 6),
    ("Nob Hill", "Haight-Ashbury", 13),
    ("Nob Hill", "North Beach", 8),
    ("Nob Hill", "Russian Hill", 5),
    ("Nob Hill", "Embarcadero", 9),
    ("Chinatown", "Marina District", 12),
    ("Chinatown", "Bayview", 20),
    ("Chinatown", "Sunset District", 29),
    ("Chinatown", "Richmond District", 20),
    ("Chinatown", "Nob Hill", 9),
    ("Chinatown", "Haight-Ashbury", 19),
    ("Chinatown", "North Beach", 3),
    ("Chinatown", "Russian Hill", 7),
    ("Chinatown", "Embarcadero", 5),
    ("Haight-Ashbury", "Marina District", 17),
    ("Haight-Ashbury", "Bayview", 18),
    ("Haight-Ashbury", "Sunset District", 15),
    ("Haight-Ashbury", "Richmond District", 10),
    ("Haight-Ashbury", "Nob Hill", 15),
    ("Haight-Ashbury", "Chinatown", 19),
    ("Haight-Ashbury", "North Beach", 19),
    ("Haight-Ashbury", "Russian Hill", 17),
    ("Haight-Ashbury", "Embarcadero", 20),
    ("North Beach", "Marina District", 9),
    ("North Beach", "Bayview", 25),
    ("North Beach", "Sunset District", 27),
    ("North Beach", "Richmond District", 18),
    ("North Beach", "Nob Hill", 7),
    ("North Beach", "Chinatown", 6),
    ("North Beach", "Haight-Ashbury", 18),
    ("North Beach", "Russian Hill", 4),
    ("North Beach", "Embarcadero", 6),
    ("Russian Hill", "Marina District", 7),
    ("Russian Hill", "Bayview", 23),
    ("Russian Hill", "Sunset District", 23),
    ("Russian Hill", "Richmond District", 14),
    ("Russian Hill", "Nob Hill", 5),
    ("Russian Hill", "Chinatown", 9),
    ("Russian Hill", "Haight-Ashbury", 17),
    ("Russian Hill", "North Beach", 5),
    ("Russian Hill", "Embarcadero", 8),
    ("Embarcadero", "Marina District", 12),
    ("Embarcadero", "Bayview", 21),
    ("Embarcadero", "Sunset District", 30),
    ("Embarcadero", "Richmond District", 21),
    ("Embarcadero", "Nob Hill", 10),
    ("Embarcadero", "Chinatown", 7),
    ("Embarcadero", "Haight-Ashbury", 21),
    ("Embarcadero", "North Beach", 5),
    ("Embarcadero", "Russian Hill", 8)
]

# Build travel time dictionary
travel = {}
for from_loc, to_loc, time_val in travel_times:
    if from_loc not in travel:
        travel[from_loc] = {}
    travel[from_loc][to_loc] = time_val

# Compute min_start and max_start for each friend
min_starts = []
max_starts = []
districts = []
durations = []
for i, (name, district, dur, start_str, end_str) in enumerate(friends):
    start_min = time_to_minutes(start_str)
    end_min = time_to_minutes(end_str)
    travel_time_from_marina = travel['Marina District'][district]
    min_start = max(travel_time_from_marina, start_min)
    max_start = end_min - dur
    min_starts.append(min_start)
    max_starts.append(max_start)
    districts.append(district)
    durations.append(dur)

# Create Z3 solver and variables
s = Optimize()
held = [Bool(f'held_{i}') for i in range(9)]
t = [Int(f't_{i}') for i in range(9)]

# Add constraints for each friend
for i in range(9):
    s.add(Implies(held[i], And(t[i] >= min_starts[i], t[i] <= max_starts[i])))

# Add disjunctive constraints for every pair of friends
for i in range(9):
    for j in range(i+1, 9):
        constraint = Implies(
            And(held[i], held[j]),
            Or(
                t[j] >= t[i] + durations[i] + travel[districts[i]][districts[j]],
                t[i] >= t[j] + durations[j] + travel[districts[j]][districts[i]]
            )
        )
        s.add(constraint)

# Maximize the number of friends met
s.maximize(Sum([If(held[i], 1, 0) for i in range(9)]))

# Check and get the model
if s.check() == sat:
    m = s.model()
    held_meetings = []
    for i in range(9):
        if is_true(m[held[i]]):
            start_val = m[t[i]].as_long()
            end_val = start_val + durations[i]
            start_str = minutes_to_time(start_val)
            end_str = minutes_to_time(end_val)
            held_meetings.append((start_val, {
                "action": "meet",
                "person": friends[i][0],
                "start_time": start_str,
                "end_time": end_str
            }))
    # Sort meetings by start time
    held_meetings.sort(key=lambda x: x[0])
    itinerary = [entry for (_, entry) in held_meetings]
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print('{"itinerary": []}')