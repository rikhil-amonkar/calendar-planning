from z3 import *
import json

# Define locations
locations = Datatype('Location')
locations.declare('FD')  # Financial District
locations.declare('FW')  # Fisherman's Wharf
locations.declare('P')   # Presidio
locations.declare('B')   # Bayview
locations.declare('HA')  # Haight-Ashbury
locations.declare('RH')  # Russian Hill
locations.declare('C')   # The Castro
locations.declare('MD')  # Marina District
locations.declare('RD')  # Richmond District
locations.declare('US')  # Union Square
locations.declare('SD')  # Sunset District
Location = locations.create()

# Define friends
friends = [
    {
        'name': 'Mark',
        'location': Location.FW,
        'available_start': 495,  # 8:15 AM
        'available_end': 600,    # 10:00 AM
        'duration': 30
    },
    {
        'name': 'Stephanie',
        'location': Location.P,
        'available_start': 735,  # 12:15 PM
        'available_end': 900,    # 3:00 PM
        'duration': 75
    },
    {
        'name': 'Betty',
        'location': Location.B,
        'available_start': 435,  # 7:15 AM
        'available_end': 1230,   # 8:30 PM
        'duration': 15
    },
    {
        'name': 'Lisa',
        'location': Location.HA,
        'available_start': 930,  # 3:30 PM
        'available_end': 1110,   # 6:30 PM
        'duration': 45
    },
    {
        'name': 'William',
        'location': Location.RH,
        'available_start': 1125, # 6:45 PM
        'available_end': 1200,   # 8:00 PM
        'duration': 60
    },
    {
        'name': 'Brian',
        'location': Location.C,
        'available_start': 555,  # 9:15 AM
        'available_end': 795,    # 1:15 PM
        'duration': 30
    },
    {
        'name': 'Joseph',
        'location': Location.MD,
        'available_start': 645,  # 10:45 AM
        'available_end': 900,    # 3:00 PM
        'duration': 90
    },
    {
        'name': 'Ashley',
        'location': Location.RD,
        'available_start': 585,  # 9:45 AM
        'available_end': 675,    # 11:15 AM
        'duration': 45
    },
    {
        'name': 'Patricia',
        'location': Location.US,
        'available_start': 990,  # 4:30 PM
        'available_end': 1200,   # 8:00 PM
        'duration': 120
    },
    {
        'name': 'Karen',
        'location': Location.SD,
        'available_start': 990,  # 4:30 PM
        'available_end': 1320,   # 10:00 PM
        'duration': 105
    },
]

# Create a map from location to friend
friend_locations = {f['location']: f for f in friends}

# Define travel_time function
travel_time = Function('travel_time', Location, Location, IntSort())

# Create solver
opt = Optimize()

# Define variables for steps 1 to 10 (0-based index)
is_used = [Bool('is_used_{}'.format(i)) for i in range(10)]
loc = [Const('loc_{}'.format(i), Location) for i in range(10)]
start = [Int('start_{}'.format(i)) for i in range(10)]
end = [Int('end_{}'.format(i)) for i in range(10)]
arrival_time = [Int('arrival_time_{}'.format(i)) for i in range(10)]

# Add constraints for travel_time
opt.add(travel_time(Location.FD, Location.FW) == 10)
opt.add(travel_time(Location.FD, Location.P) == 22)
opt.add(travel_time(Location.FD, Location.B) == 19)
opt.add(travel_time(Location.FD, Location.HA) == 19)
opt.add(travel_time(Location.FD, Location.RH) == 11)
opt.add(travel_time(Location.FD, Location.C) == 20)
opt.add(travel_time(Location.FD, Location.MD) == 15)
opt.add(travel_time(Location.FD, Location.RD) == 21)
opt.add(travel_time(Location.FD, Location.US) == 9)
opt.add(travel_time(Location.FD, Location.SD) == 30)

opt.add(travel_time(Location.FW, Location.FD) == 11)
opt.add(travel_time(Location.FW, Location.P) == 17)
opt.add(travel_time(Location.FW, Location.B) == 26)
opt.add(travel_time(Location.FW, Location.HA) == 22)
opt.add(travel_time(Location.FW, Location.RH) == 7)
opt.add(travel_time(Location.FW, Location.C) == 27)
opt.add(travel_time(Location.FW, Location.MD) == 9)
opt.add(travel_time(Location.FW, Location.RD) == 18)
opt.add(travel_time(Location.FW, Location.US) == 13)
opt.add(travel_time(Location.FW, Location.SD) == 27)

opt.add(travel_time(Location.P, Location.FD) == 23)
opt.add(travel_time(Location.P, Location.FW) == 19)
opt.add(travel_time(Location.P, Location.B) == 31)
opt.add(travel_time(Location.P, Location.HA) == 15)
opt.add(travel_time(Location.P, Location.RH) == 14)
opt.add(travel_time(Location.P, Location.C) == 21)
opt.add(travel_time(Location.P, Location.MD) == 11)
opt.add(travel_time(Location.P, Location.RD) == 7)
opt.add(travel_time(Location.P, Location.US) == 22)
opt.add(travel_time(Location.P, Location.SD) == 15)

opt.add(travel_time(Location.B, Location.FD) == 19)
opt.add(travel_time(Location.B, Location.FW) == 25)
opt.add(travel_time(Location.B, Location.P) == 32)
opt.add(travel_time(Location.B, Location.HA) == 19)
opt.add(travel_time(Location.B, Location.RH) == 23)
opt.add(travel_time(Location.B, Location.C) == 19)
opt.add(travel_time(Location.B, Location.MD) == 27)
opt.add(travel_time(Location.B, Location.RD) == 25)
opt.add(travel_time(Location.B, Location.US) == 18)
opt.add(travel_time(Location.B, Location.SD) == 23)

opt.add(travel_time(Location.HA, Location.FD) == 21)
opt.add(travel_time(Location.HA, Location.FW) == 23)
opt.add(travel_time(Location.HA, Location.P) == 15)
opt.add(travel_time(Location.HA, Location.B) == 18)
opt.add(travel_time(Location.HA, Location.RH) == 17)
opt.add(travel_time(Location.HA, Location.C) == 6)
opt.add(travel_time(Location.HA, Location.MD) == 17)
opt.add(travel_time(Location.HA, Location.RD) == 10)
opt.add(travel_time(Location.HA, Location.US) == 19)
opt.add(travel_time(Location.HA, Location.SD) == 15)

opt.add(travel_time(Location.RH, Location.FD) == 11)
opt.add(travel_time(Location.RH, Location.FW) == 7)
opt.add(travel_time(Location.RH, Location.P) == 14)
opt.add(travel_time(Location.RH, Location.B) == 23)
opt.add(travel_time(Location.RH, Location.HA) == 17)
opt.add(travel_time(Location.RH, Location.C) == 21)
opt.add(travel_time(Location.RH, Location.MD) == 7)
opt.add(travel_time(Location.RH, Location.RD) == 14)
opt.add(travel_time(Location.RH, Location.US) == 10)
opt.add(travel_time(Location.RH, Location.SD) == 23)

opt.add(travel_time(Location.C, Location.FD) == 21)
opt.add(travel_time(Location.C, Location.FW) == 24)
opt.add(travel_time(Location.C, Location.P) == 20)
opt.add(travel_time(Location.C, Location.B) == 19)
opt.add(travel_time(Location.C, Location.HA) == 6)
opt.add(travel_time(Location.C, Location.RH) == 18)
opt.add(travel_time(Location.C, Location.MD) == 21)
opt.add(travel_time(Location.C, Location.RD) == 16)
opt.add(travel_time(Location.C, Location.US) == 19)
opt.add(travel_time(Location.C, Location.SD) == 17)

opt.add(travel_time(Location.MD, Location.FD) == 17)
opt.add(travel_time(Location.MD, Location.FW) == 10)
opt.add(travel_time(Location.MD, Location.P) == 10)
opt.add(travel_time(Location.MD, Location.B) == 27)
opt.add(travel_time(Location.MD, Location.HA) == 16)
opt.add(travel_time(Location.MD, Location.RH) == 8)
opt.add(travel_time(Location.MD, Location.C) == 22)
opt.add(travel_time(Location.MD, Location.RD) == 11)
opt.add(travel_time(Location.MD, Location.US) == 16)
opt.add(travel_time(Location.MD, Location.SD) == 19)

opt.add(travel_time(Location.RD, Location.FD) == 22)
opt.add(travel_time(Location.RD, Location.FW) == 18)
opt.add(travel_time(Location.RD, Location.P) == 7)
opt.add(travel_time(Location.RD, Location.B) == 27)
opt.add(travel_time(Location.RD, Location.HA) == 10)
opt.add(travel_time(Location.RD, Location.RH) == 13)
opt.add(travel_time(Location.RD, Location.C) == 16)
opt.add(travel_time(Location.RD, Location.MD) == 9)
opt.add(travel_time(Location.RD, Location.US) == 21)
opt.add(travel_time(Location.RD, Location.SD) == 11)

opt.add(travel_time(Location.US, Location.FD) == 9)
opt.add(travel_time(Location.US, Location.FW) == 15)
opt.add(travel_time(Location.US, Location.P) == 24)
opt.add(travel_time(Location.US, Location.B) == 15)
opt.add(travel_time(Location.US, Location.HA) == 18)
opt.add(travel_time(Location.US, Location.RH) == 13)
opt.add(travel_time(Location.US, Location.C) == 17)
opt.add(travel_time(Location.US, Location.MD) == 18)
opt.add(travel_time(Location.US, Location.RD) == 20)
opt.add(travel_time(Location.US, Location.SD) == 27)

opt.add(travel_time(Location.SD, Location.FD) == 30)
opt.add(travel_time(Location.SD, Location.FW) == 29)
opt.add(travel_time(Location.SD, Location.P) == 16)
opt.add(travel_time(Location.SD, Location.B) == 22)
opt.add(travel_time(Location.SD, Location.HA) == 15)
opt.add(travel_time(Location.SD, Location.RH) == 24)
opt.add(travel_time(Location.SD, Location.C) == 17)
opt.add(travel_time(Location.SD, Location.MD) == 21)
opt.add(travel_time(Location.SD, Location.RD) == 12)
opt.add(travel_time(Location.SD, Location.US) == 30)

# Add constraints for steps
# For each step i >= 1, if is_used[i], then is_used[i-1]
for i in range(1, 10):
    opt.add(Implies(is_used[i], is_used[i-1]))

# Arrival time constraints
for i in range(10):
    if i == 0:
        # Step 1
        opt.add(Implies(is_used[i], arrival_time[i] == 540 + travel_time(Location.FD, loc[i])))
    else:
        # Step i+1
        opt.add(Implies(is_used[i], arrival_time[i] == end[i-1] + travel_time(loc[i-1], loc[i])))

# Start time >= arrival time
for i in range(10):
    opt.add(Implies(is_used[i], start[i] >= arrival_time[i]))

# Location is not FD
for i in range(10):
    opt.add(Implies(is_used[i], Not(loc[i] == Location.FD)))

# Friend constraints
for i in range(10):
    for f in friends:
        opt.add(Implies(And(is_used[i], loc[i] == f['location']), And(
            start[i] >= f['available_start'],
            end[i] <= f['available_end'],
            end[i] == start[i] + f['duration']
        )))

# Objective: maximize the number of friends met
objective = Sum([If(is_used[i], 1, 0) for i in range(10)])
opt.maximize(objective)

# Check and get model
if opt.check() == sat:
    m = opt.model()
    itinerary = []
    for i in range(10):
        if is_true(m.eval(is_used[i])):
            loc_i = m.eval(loc[i])
            friend = friend_locations[loc_i]
            start_i = m.eval(start[i]).as_long()
            end_i = m.eval(end[i]).as_long()
            start_time = f"{(start_i // 60):02}:{(start_i % 60):02}"
            end_time = f"{(end_i // 60):02}:{(end_i % 60):02}"
            itinerary.append({
                "action": "meet",
                "person": friend['name'],
                "start_time": start_time,
                "end_time": end_time
            })
    print(json.dumps({"itinerary": itinerary}))
else:
    print("No solution found.")