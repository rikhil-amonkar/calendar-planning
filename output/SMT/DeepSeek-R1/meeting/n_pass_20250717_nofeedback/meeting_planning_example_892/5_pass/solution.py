from z3 import *
import json

# Define the mapping for location names
name_map = {
    "Marina District": "Marina",
    "Bayview": "Bayview",
    "Sunset District": "Sunset",
    "Richmond District": "Richmond",
    "Nob Hill": "Nob Hill",
    "Chinatown": "Chinatown",
    "Haight-Ashbury": "Haight-Ashbury",
    "North Beach": "North Beach",
    "Russian Hill": "Russian Hill",
    "Embarcadero": "Embarcadero"
}

# Travel time data as a multi-line string
travel_text = """
Marina District to Bayview: 27.
Marina District to Sunset District: 19.
Marina District to Richmond District: 11.
Marina District to Nob Hill: 12.
Marina District to Chinatown: 15.
Marina District to Haight-Ashbury: 16.
Marina District to North Beach: 11.
Marina District to Russian Hill: 8.
Marina District to Embarcadero: 14.
Bayview to Marina District: 27.
Bayview to Sunset District: 23.
Bayview to Richmond District: 25.
Bayview to Nob Hill: 20.
Bayview to Chinatown: 19.
Bayview to Haight-Ashbury: 19.
Bayview to North Beach: 22.
Bayview to Russian Hill: 23.
Bayview to Embarcadero: 19.
Sunset District to Marina District: 21.
Sunset District to Bayview: 22.
Sunset District to Richmond District: 12.
Sunset District to Nob Hill: 27.
Sunset District to Chinatown: 30.
Sunset District to Haight-Ashbury: 15.
Sunset District to North Beach: 28.
Sunset District to Russian Hill: 24.
Sunset District to Embarcadero: 30.
Richmond District to Marina District: 9.
Richmond District to Bayview: 27.
Richmond District to Sunset District: 11.
Richmond District to Nob Hill: 17.
Richmond District to Chinatown: 20.
Richmond District to Haight-Ashbury: 10.
Richmond District to North Beach: 17.
Richmond District to Russian Hill: 13.
Richmond District to Embarcadero: 19.
Nob Hill to Marina District: 11.
Nob Hill to Bayview: 19.
Nob Hill to Sunset District: 24.
Nob Hill to Richmond District: 14.
Nob Hill to Chinatown: 6.
Nob Hill to Haight-Ashbury: 13.
Nob Hill to North Beach: 8.
Nob Hill to Russian Hill: 5.
Nob Hill to Embarcadero: 9.
Chinatown to Marina District: 12.
Chinatown to Bayview: 20.
Chinatown to Sunset District: 29.
Chinatown to Richmond District: 20.
Chinatown to Nob Hill: 9.
Chinatown to Haight-Ashbury: 19.
Chinatown to North Beach: 3.
Chinatown to Russian Hill: 7.
Chinatown to Embarcadero: 5.
Haight-Ashbury to Marina District: 17.
Haight-Ashbury to Bayview: 18.
Haight-Ashbury to Sunset District: 15.
Haight-Ashbury to Richmond District: 10.
Haight-Ashbury to Nob Hill: 15.
Haight-Ashbury to Chinatown: 19.
Haight-Ashbury to North Beach: 19.
Haight-Ashbury to Russian Hill: 17.
Haight-Ashbury to Embarcadero: 20.
North Beach to Marina District: 9.
North Beach to Bayview: 25.
North Beach to Sunset District: 27.
North Beach to Richmond District: 18.
North Beach to Nob Hill: 7.
North Beach to Chinatown: 6.
North Beach to Haight-Ashbury: 18.
North Beach to Russian Hill: 4.
North Beach to Embarcadero: 6.
Russian Hill to Marina District: 7.
Russian Hill to Bayview: 23.
Russian Hill to Sunset District: 23.
Russian Hill to Richmond District: 14.
Russian Hill to Nob Hill: 5.
Russian Hill to Chinatown: 9.
Russian Hill to Haight-Ashbury: 17.
Russian Hill to North Beach: 5.
Russian Hill to Embarcadero: 8.
Embarcadero to Marina District: 12.
Embarcadero to Bayview: 21.
Embarcadero to Sunset District: 30.
Embarcadero to Richmond District: 21.
Embarcadero to Nob Hill: 10.
Embarcadero to Chinatown: 7.
Embarcadero to Haight-Ashbury: 21.
Embarcadero to North Beach: 5.
Embarcadero to Russian Hill: 8.
"""

# Parse the travel text to build a travel time dictionary
travel_dict = {}
lines = travel_text.strip().split('\n')
for line in lines:
    line = line.strip()
    if not line:
        continue
    if line.endswith('.'):
        line = line[:-1]
    parts = line.split(' to ')
    if len(parts) < 2:
        continue
    from_place = parts[0].strip()
    rest = ' to '.join(parts[1:])
    if ':' not in rest:
        continue
    parts2 = rest.split(':')
    to_place = parts2[0].strip()
    time_val = int(parts2[1].strip())
    
    from_std = name_map.get(from_place, from_place)
    to_std = name_map.get(to_place, to_place)
    
    if from_std not in travel_dict:
        travel_dict[from_std] = {}
    travel_dict[from_std][to_std] = time_val

# Ensure all locations are in the dictionary
all_locations = set(name_map.values())
for loc in all_locations:
    if loc not in travel_dict:
        travel_dict[loc] = {}
    for loc2 in all_locations:
        if loc2 not in travel_dict[loc]:
            if loc == loc2:
                travel_dict[loc][loc2] = 0
            elif loc2 in travel_dict and loc in travel_dict[loc2]:
                travel_dict[loc][loc2] = travel_dict[loc2][loc]
            else:
                travel_dict[loc][loc2] = 10000

# Define the meetings
meetings = [
    {"name": "Charles", "location": "Bayview", "available_start": (11,30), "available_end": (14,30), "min_duration": 45},
    {"name": "Robert", "location": "Sunset", "available_start": (16,45), "available_end": (21,00), "min_duration": 30},
    {"name": "Karen", "location": "Richmond", "available_start": (19,15), "available_end": (21,30), "min_duration": 60},
    {"name": "Rebecca", "location": "Nob Hill", "available_start": (16,15), "available_end": (20,30), "min_duration": 90},
    {"name": "Margaret", "location": "Chinatown", "available_start": (14,15), "available_end": (19,45), "min_duration": 120},
    {"name": "Patricia", "location": "Haight-Ashbury", "available_start": (14,30), "available_end": (20,30), "min_duration": 45},
    {"name": "Mark", "location": "North Beach", "available_start": (14,00), "available_end": (18,30), "min_duration": 105},
    {"name": "Melissa", "location": "Russian Hill", "available_start": (13,00), "available_end": (19,45), "min_duration": 30},
    {"name": "Laura", "location": "Embarcadero", "available_start": (7,45), "available_end": (13,15), "min_duration": 105}
]

# Convert time to minutes from 9:00 AM
def to_minutes_from_9am(hour, minute):
    return (hour * 60 + minute) - (9 * 60)

for mtg in meetings:
    h1, m1 = mtg["available_start"]
    h2, m2 = mtg["available_end"]
    mtg["start_min"] = to_minutes_from_9am(h1, m1)
    mtg["end_min"] = to_minutes_from_9am(h2, m2)

# Create Z3 variables
meet_vars = [Bool(f"meet_{i}") for i in range(9)]
start_vars = [Int(f"start_{i}") for i in range(9)]
end_vars = [Int(f"end_{i}") for i in range(9)]
first_vars = [Bool(f"first_{i}") for i in range(9)]

# Create an optimizer
opt = Optimize()

# Exactly one first meeting
first_list = [If(first_vars[i], 1, 0) for i in range(9)]
total_first = Sum(first_list)
opt.add(total_first == 1)

# First meeting must be scheduled
for i in range(9):
    opt.add(Implies(first_vars[i], meet_vars[i]))

# The first meeting must be the earliest scheduled meeting
for i in range(9):
    for j in range(9):
        if i != j:
            # If i is first and j is scheduled, then i must start before j
            opt.add(Implies(And(first_vars[i], meet_vars[j]), start_vars[i] <= start_vars[j]))

# For the first meeting, account for travel time from Marina
for i in range(9):
    mtg = meetings[i]
    travel_time = travel_dict["Marina"][mtg["location"]]
    opt.add(Implies(first_vars[i], start_vars[i] >= travel_time))

# Add constraints for each meeting: availability and duration
for i in range(9):
    mtg = meetings[i]
    opt.add(Implies(meet_vars[i], start_vars[i] >= mtg["start_min"]))
    opt.add(Implies(meet_vars[i], end_vars[i] == start_vars[i] + mtg["min_duration"]))
    opt.add(Implies(meet_vars[i], end_vars[i] <= mtg["end_min"]))

# Add disjunctive constraints for each pair of meetings
for i in range(9):
    for j in range(i+1, 9):
        loc_i = meetings[i]["location"]
        loc_j = meetings[j]["location"]
        travel_ij = travel_dict[loc_i][loc_j]
        travel_ji = travel_dict[loc_j][loc_i]
        
        opt.add(Implies(And(meet_vars[i], meet_vars[j]),
                        Or(start_vars[i] >= end_vars[j] + travel_ji, 
                           start_vars[j] >= end_vars[i] + travel_ij)))

# Maximize the number of meetings
total_meetings = Sum([If(meet_vars[i], 1, 0) for i in range(9)])
opt.maximize(total_meetings)

# Solve the problem
if opt.check() == sat:
    m = opt.model()
    scheduled_meetings = []
    for i in range(9):
        if is_true(m.eval(meet_vars[i])):
            start_min = m.eval(start_vars[i]).as_long()
            end_min = m.eval(end_vars[i]).as_long()
            start_hour = 9 + start_min // 60
            start_minute = start_min % 60
            end_hour = 9 + end_min // 60
            end_minute = end_min % 60
            scheduled_meetings.append({
                "action": "meet",
                "person": meetings[i]["name"],
                "start_time": f"{start_hour:02d}:{start_minute:02d}",
                "end_time": f"{end_hour:02d}:{end_minute:02d}"
            })
    # Sort by start time
    scheduled_meetings.sort(key=lambda x: x["start_time"])
    result = {"itinerary": scheduled_meetings}
    print("SOLUTION:")
    print(json.dumps(result, indent=2))
else:
    print("No solution found")