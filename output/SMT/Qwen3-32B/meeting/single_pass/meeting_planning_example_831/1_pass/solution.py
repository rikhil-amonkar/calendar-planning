from z3 import *
import json

# Define friends and their data
friends = [
    {
        'name': 'Jeffrey',
        'location': "Fisherman's Wharf",
        'available_start': 10*60 + 15,
        'available_end': 13*60 + 0,
        'required': 90,
    },
    {
        'name': 'Ronald',
        'location': 'Alamo Square',
        'available_start': 7*60 + 45,
        'available_end': 14*60 + 45,
        'required': 120,
    },
    {
        'name': 'Jason',
        'location': 'Financial District',
        'available_start': 10*60 + 45,
        'available_end': 16*60 + 0,
        'required': 105,
    },
    {
        'name': 'Melissa',
        'location': 'Union Square',
        'available_start': 17*60 + 45,
        'available_end': 18*60 + 15,
        'required': 15,
    },
    {
        'name': 'Elizabeth',
        'location': 'Sunset District',
        'available_start': 14*60 + 45,
        'available_end': 17*60 + 30,
        'required': 105,
    },
    {
        'name': 'Margaret',
        'location': 'Embarcadero',
        'available_start': 13*60 + 15,
        'available_end': 19*60 + 0,
        'required': 90,
    },
    {
        'name': 'George',
        'location': 'Golden Gate Park',
        'available_start': 19*60 + 0,
        'available_end': 22*60 + 0,
        'required': 75,
    },
    {
        'name': 'Richard',
        'location': 'Chinatown',
        'available_start': 9*60 + 30,
        'available_end': 21*60 + 0,
        'required': 15,
    },
    {
        'name': 'Laura',
        'location': 'Richmond District',
        'available_start': 9*60 + 45,
        'available_end': 18*60 + 0,
        'required': 60,
    },
]

# Define travel times between locations
travel_times = {
    # Presidio to others
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Richmond District"): 7,
    # Fisherman's Wharf to others
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Alamo Square"): 21,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Fisherman's Wharf", "Union Square"): 13,
    ("Fisherman's Wharf", "Sunset District"): 27,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Richmond District"): 18,
    # Alamo Square to others
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Union Square"): 14,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Embarcadero"): 16,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Chinatown"): 15,
    ("Alamo Square", "Richmond District"): 11,
    # Financial District to others
    ("Financial District", "Presidio"): 22,
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Sunset District"): 30,
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Chinatown"): 5,
    ("Financial District", "Richmond District"): 21,
    # Union Square to others
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Sunset District"): 27,
    ("Union Square", "Embarcadero"): 11,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Richmond District"): 20,
    # Sunset District to others
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Fisherman's Wharf"): 29,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Embarcadero"): 30,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Richmond District"): 12,
    # Embarcadero to others
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Alamo Square"): 19,
    ("Embarcadero", "Financial District"): 5,
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "Sunset District"): 30,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Chinatown"): 7,
    ("Embarcadero", "Richmond District"): 21,
    # Golden Gate Park to others
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Alamo Square"): 9,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Richmond District"): 7,
    # Chinatown to others
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Fisherman's Wharf"): 8,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Financial District"): 5,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "Embarcadero"): 5,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Richmond District"): 20,
    # Richmond District to others
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Alamo Square"): 13,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "Union Square"): 21,
    ("Richmond District", "Sunset District"): 11,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Chinatown"): 20,
}

# Create Z3 solver
opt = Optimize()

# Number of friends
n = len(friends)

# Create variables
included = [Bool(f"included_{i}") for i in range(n)]
start = [Int(f"start_{i}") for i in range(n)]
end = [Int(f"end_{i}") for i in range(n)]

# Add constraints for each friend
for i in range(n):
    loc = friends[i]['location']
    travel_time = travel_times[('Presidio', loc)]
    available_start = friends[i]['available_start']
    available_end = friends[i]['available_end']
    required = friends[i]['required']
    
    # If included, start >= available_start
    opt.add(Implies(included[i], start[i] >= available_start))
    # If included, end <= available_end
    opt.add(Implies(included[i], end[i] <= available_end))
    # If included, end - start >= required
    opt.add(Implies(included[i], end[i] - start[i] >= required))
    # If included, start >= 9:00 AM + travel time
    opt.add(Implies(included[i], start[i] >= 540 + travel_time))

# Add constraints for all pairs of friends
for i in range(n):
    for j in range(n):
        if i != j:
            loc_i = friends[i]['location']
            loc_j = friends[j]['location']
            travel_ij = travel_times[(loc_i, loc_j)]
            travel_ji = travel_times[(loc_j, loc_i)]
            # If both included, then either B's start >= A's end + travel_ij or A's start >= B's end + travel_ji
            opt.add(Implies(And(included[i], included[j]), Or(
                start[j] >= end[i] + travel_ij,
                start[i] >= end[j] + travel_ji
            )))

# Maximize the number of included friends
opt.maximize(Sum([If(included[i], 1, 0) for i in range(n)]))

# Check if the problem is satisfiable
if opt.check() == sat:
    model = opt.model()
    result = []
    for i in range(n):
        if is_true(model.evaluate(included[i])):
            s = model.evaluate(start[i]).as_long()
            e = model.evaluate(end[i]).as_long()
            name = friends[i]['name']
            # Convert to HH:MM format
            start_time = f"{(s // 60):02d}:{(s % 60):02d}"
            end_time = f"{(e // 60):02d}:{(e % 60):02d}"
            result.append({"action": "meet", "person": name, "start_time": start_time, "end_time": end_time})
    # Sort the result by start time
    result.sort(key=lambda x: x['start_time'])
    print(json.dumps({"itinerary": result}, indent=2))
else:
    print("No solution found.")