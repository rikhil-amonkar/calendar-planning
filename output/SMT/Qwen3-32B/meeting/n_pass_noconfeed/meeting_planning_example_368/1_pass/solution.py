from z3 import *
import json

# Define travel times between locations
travel_time_matrix = [
    [0, 23, 16, 21, 19],  # Bayview (0)
    [23, 0, 15, 5, 11],   # Russian Hill (1)
    [16, 13, 0, 15, 17],  # Alamo Square (2)
    [22, 4, 16, 0, 8],    # North Beach (3)
    [19, 10, 17, 7, 0]    # Financial District (4)
]

# People's locations and other parameters
loc_p = [1, 2, 3, 4]  # Joseph, Nancy, Jason, Jeffrey
available_start = [510, 660, 1005, 630]  # in minutes since midnight
available_end = [1155, 960, 1285, 945]
min_duration = [60, 90, 15, 45]

# Precompute travel times between people's locations
people_travel_time = []
for p in range(4):
    row = []
    for q in range(4):
        row.append(travel_time_matrix[loc_p[p]][loc_p[q]])
    people_travel_time.append(row)

# Helper function to get travel time between prev_p and curr_p (both 0-3)
def get_travel_time_expr(prev_p, curr_p):
    return If(prev_p == 0,
              If(curr_p == 0, people_travel_time[0][0],
                 If(curr_p == 1, people_travel_time[0][1],
                    If(curr_p == 2, people_travel_time[0][2],
                       If(curr_p == 3, people_travel_time[0][3], 0)))),
              If(prev_p == 1,
                 If(curr_p == 0, people_travel_time[1][0],
                    If(curr_p == 1, people_travel_time[1][1],
                       If(curr_p == 2, people_travel_time[1][2],
                          If(curr_p == 3, people_travel_time[1][3], 0)))),
                 If(prev_p == 2,
                    If(curr_p == 0, people_travel_time[2][0],
                       If(curr_p == 1, people_travel_time[2][1],
                          If(curr_p == 2, people_travel_time[2][2],
                             If(curr_p == 3, people_travel_time[2][3], 0)))),
                    If(prev_p == 3,
                       If(curr_p == 0, people_travel_time[3][0],
                          If(curr_p == 1, people_travel_time[3][1],
                             If(curr_p == 2, people_travel_time[3][2],
                                If(curr_p == 3, people_travel_time[3][3], 0))),
                       0)))))

# Z3 setup
s = Optimize()

# Variables for each step (0-3)
person_vars = [Int(f'person_{i}') for i in range(4)]
arrival = [Int(f'arrival_{i}') for i in range(4)]
departure = [Int(f'departure_{i}') for i in range(4)]

# Ensure person_vars are between 0 and 4 (0-3 for people, 4 for no meeting)
for p in person_vars:
    s.add(And(p >= 0, p <= 4))

# Constraint: each person can be selected at most once
for p in range(4):
    s.add(Sum([If(person_vars[i] == p, 1, 0) for i in range(4)]) <= 1)

# Constraints for each step
for i in range(4):
    # If person_i is not 4 (i.e., a meeting is scheduled)
    p = person_vars[i]
    # Arrival and departure constraints
    # Need to express conditions based on p's value (0-3)
    cond1 = If(p == 0, arrival[i] >= available_start[0],
               If(p == 1, arrival[i] >= available_start[1],
                  If(p == 2, arrival[i] >= available_start[2],
                     If(p == 3, arrival[i] >= available_start[3], True))))
    cond2 = If(p == 0, departure[i] == arrival[i] + min_duration[0],
               If(p == 1, departure[i] == arrival[i] + min_duration[1],
                  If(p == 2, departure[i] == arrival[i] + min_duration[2],
                     If(p == 3, departure[i] == arrival[i] + min_duration[3], True))))
    cond3 = If(p == 0, departure[i] <= available_end[0],
               If(p == 1, departure[i] <= available_end[1],
                  If(p == 2, departure[i] <= available_end[2],
                     If(p == 3, departure[i] <= available_end[3], True))))
    s.add(Implies(p != 4, And(cond1, cond2, cond3)))

# Constraints for arrival times based on previous step's departure
# Step 0
travel_time_0_expr = If(person_vars[0] == 0, 23,
                        If(person_vars[0] == 1, 16,
                           If(person_vars[0] == 2, 21,
                              If(person_vars[0] == 3, 19, 0))))
s.add(Implies(person_vars[0] != 4, arrival[0] == 540 + travel_time_0_expr))

# Steps 1, 2, 3
for i in range(1, 4):
    prev_p = person_vars[i-1]
    curr_p = person_vars[i]
    travel_time_expr = get_travel_time_expr(prev_p, curr_p)
    s.add(Implies(And(prev_p != 4, curr_p != 4), arrival[i] == departure[i-1] + travel_time_expr))

# Maximize the number of meetings
num_meetings = Sum([If(person_vars[i] != 4, 1, 0) for i in range(4)])
s.maximize(num_meetings)

# Check if the problem is satisfiable
if s.check() == sat:
    m = s.model()
    # Extract the itinerary
    itinerary = []
    for i in range(4):
        p_val = m.eval(person_vars[i]).as_long()
        if p_val != 4:  # a meeting is scheduled
            # Get the person's name and location
            person_names = ["Joseph", "Nancy", "Jason", "Jeffrey"]
            locations = ["Russian Hill", "Alamo Square", "North Beach", "Financial District"]
            person_name = person_names[p_val]
            location = locations[p_val]
            # Get arrival and departure times
            arrival_time = m.eval(arrival[i]).as_long()
            departure_time = m.eval(departure[i]).as_long()
            # Convert to H:MM format
            def minutes_to_time(minutes):
                hours = minutes // 60
                mins = minutes % 60
                return f"{hours}:{mins:02d}"
            start_time = minutes_to_time(arrival_time)
            end_time = minutes_to_time(departure_time)
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": person_name,
                "start_time": start_time,
                "end_time": end_time
            })
    # Output as JSON
    print(json.dumps({"itinerary": itinerary}))
else:
    print("No solution found.")