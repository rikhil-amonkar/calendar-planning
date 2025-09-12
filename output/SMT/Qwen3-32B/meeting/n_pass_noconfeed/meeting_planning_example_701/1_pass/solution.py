from z3 import *
import json

# Define friends' data
friends_data = [
    {
        'name': 'Lisa',
        'available_start': 19 * 60 + 15,  # 1155
        'available_end': 21 * 60 + 15,    # 1275
        'required_duration': 120,
    },
    {
        'name': 'Daniel',
        'available_start': 8 * 60 + 15,   # 495
        'available_end': 11 * 60 + 0,     # 660
        'required_duration': 15,
    },
    {
        'name': 'Elizabeth',
        'available_start': 21 * 60 + 15,  # 1275
        'available_end': 22 * 60 + 15,    # 1335
        'required_duration': 45,
    },
    {
        'name': 'Steven',
        'available_start': 16 * 60 + 30,  # 990
        'available_end': 20 * 60 + 45,    # 1245
        'required_duration': 90,
    },
    {
        'name': 'Timothy',
        'available_start': 12 * 60 + 0,   # 720
        'available_end': 18 * 60 + 0,     # 1080
        'required_duration': 90,
    },
    {
        'name': 'Ashley',
        'available_start': 20 * 60 + 45,  # 1245
        'available_end': 21 * 60 + 45,    # 1305
        'required_duration': 60,
    },
    {
        'name': 'Kevin',
        'available_start': 12 * 60 + 0,   # 720
        'available_end': 19 * 60 + 0,     # 1140
        'required_duration': 30,
    },
    {
        'name': 'Betty',
        'available_start': 13 * 60 + 15,  # 795
        'available_end': 15 * 60 + 45,    # 945
        'required_duration': 30,
    }
]

# Define friend's location indices
loc = [1, 2, 3, 4, 5, 6, 7, 8]  # 0: Lisa (Castro), 1: Daniel (Nob Hill), etc.

# Define location names for output
location_names = [
    "Mission District",
    "The Castro",
    "Nob Hill",
    "Presidio",
    "Marina District",
    "Pacific Heights",
    "Golden Gate Park",
    "Chinatown",
    "Richmond District"
]

# Define travel times between locations
travel_time = [[0 for _ in range(9)] for _ in range(9)]

# Fill travel_time matrix with provided data
travel_time[0][1] = 7  # Mission to Castro
travel_time[0][2] = 12  # Mission to Nob Hill
travel_time[0][3] = 25  # Mission to Presidio
travel_time[0][4] = 19  # Mission to Marina
travel_time[0][5] = 16  # Mission to Pacific Heights
travel_time[0][6] = 17  # Mission to Golden Gate Park
travel_time[0][7] = 16  # Mission to Chinatown
travel_time[0][8] = 20  # Mission to Richmond

travel_time[1][0] = 7  # Castro to Mission
travel_time[1][2] = 16  # Castro to Nob Hill
travel_time[1][3] = 20  # Castro to Presidio
travel_time[1][4] = 21  # Castro to Marina
travel_time[1][5] = 16  # Castro to Pacific Heights
travel_time[1][6] = 11  # Castro to Golden Gate Park
travel_time[1][7] = 22  # Castro to Chinatown
travel_time[1][8] = 16  # Castro to Richmond

travel_time[2][0] = 13  # Nob Hill to Mission
travel_time[2][1] = 17  # Nob Hill to Castro
travel_time[2][3] = 17  # Nob Hill to Presidio
travel_time[2][4] = 11  # Nob Hill to Marina
travel_time[2][5] = 8  # Nob Hill to Pacific Heights
travel_time[2][6] = 17  # Nob Hill to Golden Gate Park
travel_time[2][7] = 6  # Nob Hill to Chinatown
travel_time[2][8] = 14  # Nob Hill to Richmond

travel_time[3][0] = 26  # Presidio to Mission
travel_time[3][1] = 21  # Presidio to Castro
travel_time[3][2] = 18  # Presidio to Nob Hill
travel_time[3][4] = 11  # Presidio to Marina
travel_time[3][5] = 11  # Presidio to Pacific Heights
travel_time[3][6] = 12  # Presidio to Golden Gate Park
travel_time[3][7] = 21  # Presidio to Chinatown
travel_time[3][8] = 7  # Presidio to Richmond

travel_time[4][0] = 20  # Marina to Mission
travel_time[4][1] = 22  # Marina to Castro
travel_time[4][2] = 12  # Marina to Nob Hill
travel_time[4][3] = 10  # Marina to Presidio
travel_time[4][5] = 7  # Marina to Pacific Heights
travel_time[4][6] = 18  # Marina to Golden Gate Park
travel_time[4][7] = 15  # Marina to Chinatown
travel_time[4][8] = 11  # Marina to Richmond

travel_time[5][0] = 15  # Pacific Heights to Mission
travel_time[5][1] = 16  # Pacific Heights to Castro
travel_time[5][2] = 8  # Pacific Heights to Nob Hill
travel_time[5][3] = 11  # Pacific Heights to Presidio
travel_time[5][4] = 6  # Pacific Heights to Marina
travel_time[5][6] = 15  # Pacific Heights to Golden Gate Park
travel_time[5][7] = 11  # Pacific Heights to Chinatown
travel_time[5][8] = 12  # Pacific Heights to Richmond

travel_time[6][0] = 17  # Golden Gate Park to Mission
travel_time[6][1] = 13  # Golden Gate Park to Castro
travel_time[6][2] = 20  # Golden Gate Park to Nob Hill
travel_time[6][3] = 11  # Golden Gate Park to Presidio
travel_time[6][4] = 16  # Golden Gate Park to Marina
travel_time[6][5] = 16  # Golden Gate Park to Pacific Heights
travel_time[6][7] = 23  # Golden Gate Park to Chinatown
travel_time[6][8] = 7  # Golden Gate Park to Richmond

travel_time[7][0] = 17  # Chinatown to Mission
travel_time[7][1] = 22  # Chinatown to Castro
travel_time[7][2] = 9  # Chinatown to Nob Hill
travel_time[7][3] = 19  # Chinatown to Presidio
travel_time[7][4] = 12  # Chinatown to Marina
travel_time[7][5] = 10  # Chinatown to Pacific Heights
travel_time[7][6] = 23  # Chinatown to Golden Gate Park
travel_time[7][8] = 20  # Chinatown to Richmond

travel_time[8][0] = 20  # Richmond to Mission
travel_time[8][1] = 16  # Richmond to Castro
travel_time[8][2] = 17  # Richmond to Nob Hill
travel_time[8][3] = 7  # Richmond to Presidio
travel_time[8][4] = 9  # Richmond to Marina
travel_time[8][5] = 10  # Richmond to Pacific Heights
travel_time[8][6] = 9  # Richmond to Golden Gate Park
travel_time[8][7] = 20  # Richmond to Chinatown

# Create friend_travel_time matrix
friend_travel_time = [[0 for _ in range(8)] for _ in range(8)]
for f_prev in range(8):
    for f_current in range(8):
        friend_travel_time[f_prev][f_current] = travel_time[loc[f_prev]][loc[f_current]]

# Z3 variables
meet = [Int('meet_{}'.format(i)) for i in range(8)]
start = [Int('start_{}'.format(i)) for i in range(8)]
end = [Int('end_{}'.format(i)) for i in range(8)]

solver = Optimize()

# Constraints for meet variables
for i in range(8):
    solver.add(meet[i] >= -1)
    solver.add(meet[i] <= 7)

# No duplicate friends
for i in range(8):
    for j in range(i + 1, 8):
        solver.add(Or(meet[i] == -1, meet[j] == -1, meet[i] != meet[j]))

# Sequential filling
for i in range(1, 8):
    solver.add(Implies(meet[i] != -1, meet[i - 1] != -1))

# Meeting constraints
for i in range(8):
    for f in range(8):
        available_start = friends_data[f]['available_start']
        available_end = friends_data[f]['available_end']
        required_duration = friends_data[f]['required_duration']
        solver.add(Implies(And(meet[i] == f, meet[i] != -1), start[i] >= available_start))
        solver.add(Implies(And(meet[i] == f, meet[i] != -1), end[i] <= available_end))
        solver.add(Implies(And(meet[i] == f, meet[i] != -1), end[i] >= start[i] + required_duration))

# First step travel time constraint
mission_to_friend = Sum([travel_time[0][loc[f]] * If(meet[0] == f, 1, 0) for f in range(8)])
solver.add(Implies(meet[0] != -1, start[0] >= 540 + mission_to_friend))

# Subsequent steps travel time constraints
for i in range(1, 8):
    travel_time_expr = Sum([friend_travel_time[f_prev][f_current] * If(And(meet[i - 1] == f_prev, meet[i] == f_current), 1, 0) for f_prev in range(8) for f_current in range(8)])
    solver.add(Implies(meet[i] != -1, start[i] >= end[i - 1] + travel_time_expr))

# Maximize number of friends met
count = Sum([If(meet[i] != -1, 1, 0) for i in range(8)])
solver.maximize(count)

# Solve and output
result = solver.check()
if result == sat:
    model = solver.model()
    itinerary = []
    for i in range(8):
        m = model.eval(meet[i])
        if m != -1:
            friend_index = m.as_long()
            friend = friends_data[friend_index]
            start_time = model.eval(start[i]).as_long()
            end_time = model.eval(end[i]).as_long()
            loc_index = loc[friend_index]
            itinerary.append({
                "action": "meet",
                "location": location_names[loc_index],
                "person": friend['name'],
                "start_time": f"{start_time // 60}:{start_time % 60:02d}",
                "end_time": f"{end_time // 60}:{end_time % 60:02d}"
            })
    print(json.dumps({"itinerary": itinerary}))
else:
    print(json.dumps({"itinerary": []}))