from z3 import *

# Define travel times between locations
travel_time = {
    'Presidio': {
        'Haight-Ashbury': 15,
        'Nob Hill': 18,
        'Russian Hill': 14,
        'North Beach': 18,
        'Chinatown': 21,
        'Union Square': 22,
        'Embarcadero': 20,
        'Financial District': 23,
        'Marina District': 11
    },
    'Haight-Ashbury': {
        'Presidio': 15,
        'Nob Hill': 15,
        'Russian Hill': 17,
        'North Beach': 19,
        'Chinatown': 19,
        'Union Square': 19,
        'Embarcadero': 20,
        'Financial District': 21,
        'Marina District': 17
    },
    'Nob Hill': {
        'Presidio': 17,
        'Haight-Ashbury': 13,
        'Russian Hill': 5,
        'North Beach': 8,
        'Chinatown': 6,
        'Union Square': 7,
        'Embarcadero': 9,
        'Financial District': 9,
        'Marina District': 11
    },
    'Russian Hill': {
        'Presidio': 14,
        'Haight-Ashbury': 17,
        'Nob Hill': 5,
        'North Beach': 5,
        'Chinatown': 9,
        'Union Square': 10,
        'Embarcadero': 8,
        'Financial District': 11,
        'Marina District': 7
    },
    'North Beach': {
        'Presidio': 17,
        'Haight-Ashbury': 18,
        'Nob Hill': 7,
        'Russian Hill': 4,
        'Chinatown': 6,
        'Union Square': 7,
        'Embarcadero': 6,
        'Financial District': 8,
        'Marina District': 9
    },
    'Chinatown': {
        'Presidio': 19,
        'Haight-Ashbury': 19,
        'Nob Hill': 9,
        'Russian Hill': 7,
        'North Beach': 3,
        'Union Square': 7,
        'Embarcadero': 5,
        'Financial District': 5,
        'Marina District': 12
    },
    'Union Square': {
        'Presidio': 24,
        'Haight-Ashbury': 18,
        'Nob Hill': 9,
        'Russian Hill': 13,
        'North Beach': 10,
        'Chinatown': 7,
        'Embarcadero': 11,
        'Financial District': 9,
        'Marina District': 18
    },
    'Embarcadero': {
        'Presidio': 20,
        'Haight-Ashbury': 21,
        'Nob Hill': 10,
        'Russian Hill': 8,
        'North Beach': 5,
        'Chinatown': 7,
        'Union Square': 10,
        'Financial District': 5,
        'Marina District': 12
    },
    'Financial District': {
        'Presidio': 22,
        'Haight-Ashbury': 19,
        'Nob Hill': 8,
        'Russian Hill': 11,
        'North Beach': 7,
        'Chinatown': 5,
        'Union Square': 9,
        'Embarcadero': 4,
        'Marina District': 15
    },
    'Marina District': {
        'Presidio': 10,
        'Haight-Ashbury': 16,
        'Nob Hill': 12,
        'Russian Hill': 8,
        'North Beach': 11,
        'Chinatown': 15,
        'Union Square': 16,
        'Embarcadero': 14,
        'Financial District': 17
    }
}

# Define friends data: (name, location, available_start (min), available_end (min), min_duration (min))
friends = [
    ("Karen", "Haight-Ashbury", 21*60, 21*60+45, 45),
    ("Jessica", "Nob Hill", 13*60+45, 21*60, 90),
    ("Brian", "Russian Hill", 15*60+30, 21*60+45, 60),
    ("Kenneth", "North Beach", 9*60+45, 21*60, 30),
    ("Jason", "Chinatown", 8*60+15, 11*60+45, 75),
    ("Stephanie", "Union Square", 14*60+45, 18*60+45, 105),
    ("Kimberly", "Embarcadero", 9*60+45, 19*60+30, 75),
    ("Steven", "Financial District", 7*60+15, 21*60+15, 60),
    ("Mark", "Marina District", 10*60+15, 13*60, 75)
]

# Initialize Z3 solver
s = Optimize()

# Create variables for each friend: whether to meet, start time, end time
m = [Bool(f'm_{i}') for i in range(9)]
start_vars = [Real(f's_{i}') for i in range(9)]
end_vars = [Real(f'e_{i}') for i in range(9)]

# Add constraints for each friend
for i in range(9):
    name, loc, avail_start, avail_end, dur = friends[i]
    # If meeting, then within availability window and duration constraint
    s.add(Implies(m[i], And(
        start_vars[i] >= avail_start,
        end_vars[i] <= avail_end,
        end_vars[i] == start_vars[i] + dur
    )))
    # Travel time from Presidio to friend's location
    presidio_travel = travel_time['Presidio'][loc]
    s.add(Implies(m[i], start_vars[i] >= 9*60 + presidio_travel))

# Add pairwise constraints for overlapping meetings
for i in range(9):
    for j in range(i+1, 9):
        loc_i = friends[i][1]
        loc_j = friends[j][1]
        tij = travel_time[loc_i][loc_j]
        tji = travel_time[loc_j][loc_i]
        s.add(Implies(And(m[i], m[j]), 
                     Or(end_vars[i] + tij <= start_vars[j], 
                        end_vars[j] + tji <= start_vars[i])))

# Maximize the number of meetings
s.maximize(Sum([If(m_i, 1, 0) for m_i in m]))

# Solve the problem
if s.check() == sat:
    model = s.model()
    itinerary = []
    for i in range(9):
        if model.evaluate(m[i]):
            name = friends[i][0]
            s_val = model.evaluate(start_vars[i])
            e_val = model.evaluate(end_vars[i])
            # Convert Z3 values to integers
            s_minutes = round(float(s_val.as_fraction()))
            e_minutes = round(float(e_val.as_fraction()))
            # Convert minutes to HH:MM
            s_hour = s_minutes // 60
            s_minute = s_minutes % 60
            e_hour = e_minutes // 60
            e_minute = e_minutes % 60
            start_str = f"{int(s_hour):02d}:{int(s_minute):02d}"
            end_str = f"{int(e_hour):02d}:{int(e_minute):02d}"
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": start_str,
                "end_time": end_str
            })
    # Sort itinerary by start time
    itinerary.sort(key=lambda x: x['start_time'])
    # Output the solution
    print('SOLUTION:')
    print(f'{{"itinerary": {itinerary}}}')
else:
    print("No solution found")