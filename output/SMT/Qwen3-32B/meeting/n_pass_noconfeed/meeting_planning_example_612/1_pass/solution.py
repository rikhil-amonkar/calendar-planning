from z3 import *
import json

# Define friends and their data
friends = [
    {'name': 'Deborah', 'location': 3, 'available_start': 0, 'available_end': 360, 'required_duration': 45},
    {'name': 'George', 'location': 5, 'available_start': 0, 'available_end': 305, 'required_duration': 60},
    {'name': 'Steven', 'location': 7, 'available_start': 225, 'available_end': 825, 'required_duration': 105},
    {'name': 'Emily', 'location': 1, 'available_start': 285, 'available_end': 405, 'required_duration': 105},
    {'name': 'Mark', 'location': 2, 'available_start': 435, 'available_end': 720, 'required_duration': 60},
    {'name': 'Andrew', 'location': 6, 'available_start': 765, 'available_end': 870, 'required_duration': 75},
    {'name': 'Margaret', 'location': 4, 'available_start': 840, 'available_end': 900, 'required_duration': 60},
]

# Define travel times between locations
travel_times = [
    [0, 13, 18, 16, 16, 8, 17, 9],  # Alamo Square
    [15, 0, 14, 9, 23, 21, 8, 21],  # Russian Hill
    [18, 14, 0, 21, 15, 21, 20, 12],  # Presidio
    [17, 7, 19, 0, 29, 22, 5, 23],  # Chinatown
    [17, 24, 16, 30, 0, 17, 31, 11],  # Sunset District
    [8, 18, 20, 20, 17, 0, 22, 11],  # The Castro
    [19, 8, 20, 7, 30, 25, 0, 25],  # Embarcadero
    [10, 19, 11, 23, 10, 13, 25, 0],  # Golden Gate Park
]

# Define location to name mapping
location_to_name = {
    0: 'Alamo Square',
    1: 'Russian Hill',
    2: 'Presidio',
    3: 'Chinatown',
    4: 'Sunset District',
    5: 'The Castro',
    6: 'Embarcadero',
    7: 'Golden Gate Park',
}

def minutes_to_time(minutes):
    total_minutes = 450 + minutes  # 7:30 AM is 450 minutes since midnight
    hours = total_minutes // 60
    mins = total_minutes % 60
    return f"{hours}:{mins:02d}"

def build_available_start(current_p):
    expr = 0
    for f in range(7):
        expr = If(current_p == f, friends[f]['available_start'], expr)
    return expr

def build_available_end(current_p):
    expr = 0
    for f in range(7):
        expr = If(current_p == f, friends[f]['available_end'], expr)
    return expr

def build_required_duration(current_p):
    expr = 0
    for f in range(7):
        expr = If(current_p == f, friends[f]['required_duration'], expr)
    return expr

def build_current_loc(current_p, default_loc_expr):
    expr = default_loc_expr
    for f in range(7):
        expr = If(current_p == f, friends[f]['location'], expr)
    return expr

# Z3 setup
opt = Optimize()

MAX_MEETINGS = 7
persons = [Int(f'person_{i}') for i in range(MAX_MEETINGS)]
starts = [Int(f'start_{i}') for i in range(MAX_MEETINGS)]
ends = [Int(f'end_{i}') for i in range(MAX_MEETINGS)]

# Define travel_time_func as a Z3 function
travel_time_func = Function('travel_time_func', IntSort(), IntSort(), IntSort())

# Add constraints for travel_time_func
for loc1 in range(8):
    for loc2 in range(8):
        opt.add(travel_time_func(loc1, loc2) == travel_times[loc1][loc2])

# Add constraints for persons to be between -1 and 6
for p in persons:
    opt.add(And(p >= -1, p <= 6))

# Add uniqueness constraints for persons
for i in range(MAX_MEETINGS):
    for j in range(i+1, MAX_MEETINGS):
        opt.add(Or(persons[i] == -1, persons[j] == -1, persons[i] != persons[j]))

# Initialize previous end time and location
prev_end = 90  # initial time at Alamo Square (9:00 AM is 90 minutes since 7:30 AM)
prev_loc_expr = 0  # Alamo Square's location integer

for i in range(MAX_MEETINGS):
    current_p = persons[i]
    current_s = starts[i]
    current_e = ends[i]

    # Build current_loc_expr
    current_loc_expr = build_current_loc(current_p, prev_loc_expr)

    # Build travel_time_expr
    travel_time_expr = travel_time_func(prev_loc_expr, current_loc_expr)

    # Add constraints for this position
    opt.add(Implies(current_p != -1, current_s >= prev_end + travel_time_expr))
    opt.add(Implies(current_p != -1, current_s >= build_available_start(current_p)))
    opt.add(Implies(current_p != -1, current_e == current_s + build_required_duration(current_p)))
    opt.add(Implies(current_p != -1, current_e <= build_available_end(current_p)))

    # Update previous end and location for next iteration
    new_prev_end = If(current_p != -1, current_e, prev_end)
    new_prev_loc_expr = If(current_p != -1, current_loc_expr, prev_loc_expr)

    # Update for next iteration
    prev_end = new_prev_end
    prev_loc_expr = new_prev_loc_expr

# Maximize the number of meetings
count = Sum([If(p != -1, 1, 0) for p in persons])
opt.maximize(count)

# Solve and output
if opt.check() == sat:
    model = opt.model()
    itinerary = []
    for i in range(MAX_MEETINGS):
        p = model.eval(persons[i])
        if p != -1:
            friend = friends[p.as_long()]
            s = model.eval(starts[i])
            e = model.eval(ends[i])
            start_time_str = minutes_to_time(s.as_long())
            end_time_str = minutes_to_time(e.as_long())
            itinerary.append({
                "action": "meet",
                "location": location_to_name[friend['location']],
                "person": friend['name'],
                "start_time": start_time_str,
                "end_time": end_time_str
            })
    # Sort by start time
    itinerary.sort(key=lambda x: x['start_time'])
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found.")