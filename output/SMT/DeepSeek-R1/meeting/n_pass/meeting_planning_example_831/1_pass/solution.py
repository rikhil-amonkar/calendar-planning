from z3 import *
import json

# Define travel times between locations (including Presidio)
travel_time_dict = {
    "Presidio": {
        "Fisherman's Wharf": 19,
        "Alamo Square": 19,
        "Financial District": 23,
        "Union Square": 22,
        "Sunset District": 15,
        "Embarcadero": 20,
        "Golden Gate Park": 12,
        "Chinatown": 21,
        "Richmond District": 7
    },
    "Fisherman's Wharf": {
        "Presidio": 17,
        "Alamo Square": 21,
        "Financial District": 11,
        "Union Square": 13,
        "Sunset District": 27,
        "Embarcadero": 8,
        "Golden Gate Park": 25,
        "Chinatown": 12,
        "Richmond District": 18
    },
    "Alamo Square": {
        "Presidio": 17,
        "Fisherman's Wharf": 19,
        "Financial District": 17,
        "Union Square": 14,
        "Sunset District": 16,
        "Embarcadero": 16,
        "Golden Gate Park": 9,
        "Chinatown": 15,
        "Richmond District": 11
    },
    "Financial District": {
        "Presidio": 22,
        "Fisherman's Wharf": 10,
        "Alamo Square": 17,
        "Union Square": 9,
        "Sunset District": 30,
        "Embarcadero": 4,
        "Golden Gate Park": 23,
        "Chinatown": 5,
        "Richmond District": 21
    },
    "Union Square": {
        "Presidio": 24,
        "Fisherman's Wharf": 15,
        "Alamo Square": 15,
        "Financial District": 9,
        "Sunset District": 27,
        "Embarcadero": 11,
        "Golden Gate Park": 22,
        "Chinatown": 7,
        "Richmond District": 20
    },
    "Sunset District": {
        "Presidio": 16,
        "Fisherman's Wharf": 29,
        "Alamo Square": 17,
        "Financial District": 30,
        "Union Square": 30,
        "Embarcadero": 30,
        "Golden Gate Park": 11,
        "Chinatown": 30,
        "Richmond District": 12
    },
    "Embarcadero": {
        "Presidio": 20,
        "Fisherman's Wharf": 6,
        "Alamo Square": 19,
        "Financial District": 5,
        "Union Square": 10,
        "Sunset District": 30,
        "Golden Gate Park": 25,
        "Chinatown": 7,
        "Richmond District": 21
    },
    "Golden Gate Park": {
        "Presidio": 11,
        "Fisherman's Wharf": 24,
        "Alamo Square": 9,
        "Financial District": 26,
        "Union Square": 22,
        "Sunset District": 10,
        "Embarcadero": 25,
        "Chinatown": 23,
        "Richmond District": 7
    },
    "Chinatown": {
        "Presidio": 19,
        "Fisherman's Wharf": 8,
        "Alamo Square": 17,
        "Financial District": 5,
        "Union Square": 7,
        "Sunset District": 29,
        "Embarcadero": 5,
        "Golden Gate Park": 23,
        "Richmond District": 20
    },
    "Richmond District": {
        "Presidio": 7,
        "Fisherman's Wharf": 18,
        "Alamo Square": 13,
        "Financial District": 22,
        "Union Square": 21,
        "Sunset District": 11,
        "Embarcadero": 19,
        "Golden Gate Park": 9,
        "Chinatown": 20
    }
}

# Friend data: names, locations, time windows, and min meeting times
friend_data = [
    {"name": "Jeffrey", "location": "Fisherman's Wharf", "start_avail": 75, "end_avail": 240, "min_time": 90},
    {"name": "Ronald", "location": "Alamo Square", "start_avail": 0, "end_avail": 345, "min_time": 120},
    {"name": "Jason", "location": "Financial District", "start_avail": 105, "end_avail": 420, "min_time": 105},
    {"name": "Melissa", "location": "Union Square", "start_avail": 525, "end_avail": 555, "min_time": 15},
    {"name": "Elizabeth", "location": "Sunset District", "start_avail": 345, "end_avail": 510, "min_time": 105},
    {"name": "Margaret", "location": "Embarcadero", "start_avail": 255, "end_avail": 600, "min_time": 90},
    {"name": "George", "location": "Golden Gate Park", "start_avail": 600, "end_avail": 780, "min_time": 75},
    {"name": "Richard", "location": "Chinatown", "start_avail": 30, "end_avail": 720, "min_time": 15},
    {"name": "Laura", "location": "Richmond District", "start_avail": 45, "end_avail": 540, "min_time": 60}
]

# Travel times from Presidio to each friend's location
travel_from_presidio = [19, 19, 23, 22, 15, 20, 12, 21, 7]

# Create Z3 variables
meet = [Bool(f'meet_{i}') for i in range(9)]
start = [Real(f'start_{i}') for i in range(9)]
next_var = [Int(f'next_{i}') for i in range(9)]  # next meeting index or 9 for end
u = [Int(f'u_{i}') for i in range(9)]  # position in sequence

# Create solver and set objective to maximize meetings
s = Optimize()
total_meetings = Sum([If(meet[i], 1, 0) for i in range(9)])
s.maximize(total_meetings)

# Helper function to get travel time between two friends
def travel_time(i, j):
    loc_i = friend_data[i]['location']
    loc_j = friend_data[j]['location']
    return travel_time_dict[loc_i][loc_j]

# Constraints for each friend
for i in range(9):
    # If meeting, must be within availability and meet min duration
    s.add(Implies(meet[i], 
                  And(start[i] >= friend_data[i]['start_avail'],
                      start[i] + friend_data[i]['min_time'] <= friend_data[i]['end_avail'])))
    
    # If meeting, next must be valid (another meeting or end)
    other_meetings = [And(meet[j], next_var[i] == j) for j in range(9) if j != i]
    s.add(Implies(meet[i], Or(other_meetings + [next_var[i] == 9])))
    
    # First meeting or after another meeting
    no_prev_conditions = []
    for j in range(9):
        if j == i:
            continue
        # If j is met and next points to i, then constraint
        cond = And(meet[j], next_var[j] == i, 
                   start[i] >= start[j] + friend_data[j]['min_time'] + travel_time(j, i))
        no_prev_conditions.append(cond)
    # If no previous meeting points to i, then must be first meeting
    s.add(Implies(meet[i],
                  Or(
                      And(
                          # No j has next_var[j] == i
                          And([Implies(meet[j], next_var[j] != i) for j in range(9) if j != i]),
                          start[i] >= travel_from_presidio[i]
                      ),
                      Or(no_prev_conditions)
                  )))

# MTZ constraints to prevent cycles
for i in range(9):
    for j in range(9):
        if i == j:
            continue
        s.add(Implies(And(meet[i], meet[j], next_var[i] == j),
                      u[j] == u[i] + 1))
    s.add(Implies(meet[i], And(u[i] >= 0, u[i] < 9)))

# Solve and extract solution
if s.check() == sat:
    m = s.model()
    itinerary = []
    names = [fd['name'] for fd in friend_data]
    for i in range(9):
        if is_true(m.evaluate(meet[i])):
            start_val = m.evaluate(start[i])
            # Convert Z3 rational to float
            if is_rational_value(start_val):
                start_min = float(start_val.numerator_as_long()) / float(start_val.denominator_as_long())
            elif is_algebraic_value(start_val):
                start_min = start_val.approx(10).as_fraction()
                start_min = float(start_min.numerator) / float(start_min.denominator)
            else:
                start_min = 0.0  # fallback
            
            end_min = start_min + friend_data[i]['min_time']
            # Convert to HH:MM
            total_start_min = 9*60 + start_min
            hours = int(total_start_min // 60)
            minutes = int(total_start_min % 60)
            start_str = f"{hours:02d}:{minutes:02d}"
            
            total_end_min = 9*60 + end_min
            hours_end = int(total_end_min // 60)
            minutes_end = int(total_end_min % 60)
            end_str = f"{hours_end:02d}:{minutes_end:02d}"
            
            itinerary.append({
                "action": "meet",
                "person": names[i],
                "start_time": start_str,
                "end_time": end_str
            })
    
    # Sort by start time
    itinerary.sort(key=lambda x: x['start_time'])
    print("SOLUTION:")
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("SOLUTION:\n{\"itinerary\": []}")