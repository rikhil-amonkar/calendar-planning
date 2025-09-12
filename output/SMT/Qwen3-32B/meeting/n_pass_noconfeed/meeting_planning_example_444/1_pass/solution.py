from z3 import *
import json

# Define friends' data
friends_data = [
    {'name': 'Ronald', 'available_start': 825, 'available_end': 1035, 'min_duration': 105},
    {'name': 'Patricia', 'available_start': 555, 'available_end': 1320, 'min_duration': 60},
    {'name': 'Laura', 'available_start': 750, 'available_end': 765, 'min_duration': 15},
    {'name': 'Emily', 'available_start': 975, 'available_end': 1110, 'min_duration': 60},
    {'name': 'Mary', 'available_start': 900, 'available_end': 990, 'min_duration': 60},
]

friends_locations = ['Russian Hill', 'Sunset District', 'North Beach', 'The Castro', 'Golden Gate Park']

# Travel time dictionary
travel_time_dict = {
    'Financial District': {
        'Russian Hill': 10,
        'Sunset District': 31,
        'North Beach': 7,
        'The Castro': 23,
        'Golden Gate Park': 23,
    },
    'Russian Hill': {
        'Financial District': 11,
        'Sunset District': 23,
        'North Beach': 5,
        'The Castro': 21,
        'Golden Gate Park': 21,
    },
    'Sunset District': {
        'Financial District': 30,
        'Russian Hill': 24,
        'North Beach': 29,
        'The Castro': 17,
        'Golden Gate Park': 11,
    },
    'North Beach': {
        'Financial District': 8,
        'Russian Hill': 4,
        'Sunset District': 27,
        'The Castro': 22,
        'Golden Gate Park': 22,
    },
    'The Castro': {
        'Financial District': 20,
        'Russian Hill': 18,
        'Sunset District': 17,
        'North Beach': 20,
        'Golden Gate Park': 11,
    },
    'Golden Gate Park': {
        'Financial District': 26,
        'Russian Hill': 19,
        'Sunset District': 10,
        'North Beach': 24,
        'The Castro': 13,
    },
}

# Generate travel time between friends
travel_time_between_friends = []
for i in range(5):
    loc_i = friends_locations[i]
    row = []
    for j in range(5):
        loc_j = friends_locations[j]
        row.append(travel_time_dict[loc_i][loc_j])
    travel_time_between_friends.append(row)

# Initial travel times from Financial District to each friend's location
initial_travel_times = [travel_time_dict['Financial District'][loc] for loc in friends_locations]

# Z3 solver setup
s = Optimize()

# Variables for each step (1 to 5)
met = []
friend = []
start = []
end = []
arrival = []

for i in range(1, 6):  # steps 1-5
    met_i = Bool(f'met_{i}')
    friend_i = Int(f'friend_{i}')
    start_i = Int(f'start_{i}')
    end_i = Int(f'end_{i}')
    arrival_i = Int(f'arrival_{i}')
    met.append(met_i)
    friend.append(friend_i)
    start.append(start_i)
    end.append(end_i)
    arrival.append(arrival_i)

# Constraints for each step
for i in range(5):  # 0-based index for steps 1-5
    step = i + 1
    met_i = met[i]
    friend_i = friend[i]
    start_i = start[i]
    end_i = end[i]
    arrival_i = arrival[i]

    # If met_i is True, friend_i must be between 0 and 4
    s.add(Implies(met_i, And(friend_i >= 0, friend_i <= 4)))

    # Define available_start_i, available_end_i, min_duration_i
    available_start_i = If(friend_i == 0, 825,
                           If(friend_i == 1, 555,
                              If(friend_i == 2, 750,
                                 If(friend_i == 3, 975,
                                    If(friend_i == 4, 900, 0)))))
    available_end_i = If(friend_i == 0, 1035,
                         If(friend_i == 1, 1320,
                            If(friend_i == 2, 765,
                               If(friend_i == 3, 1110,
                                  If(friend_i == 4, 990, 0)))))
    min_duration_i = If(friend_i == 0, 105,
                        If(friend_i == 1, 60,
                           If(friend_i == 2, 15,
                              If(friend_i == 3, 60,
                                 If(friend_i == 4, 60, 0)))))

    # Constraints for available time and duration
    s.add(Implies(met_i, start_i >= available_start_i))
    s.add(Implies(met_i, end_i <= available_end_i))
    s.add(Implies(met_i, end_i - start_i >= min_duration_i))

    # Define arrival_i based on previous step
    if i == 0:  # first step
        arrival_i_expr = 540 + If(friend_i == 0, 10,
                                  If(friend_i == 1, 31,
                                     If(friend_i == 2, 7,
                                        If(friend_i == 3, 23,
                                           If(friend_i == 4, 23, 0))))
        s.add(arrival_i == arrival_i_expr)
    else:
        # Generate travel time expression between previous and current friend
        prev_friend = friend[i-1]
        current_friend = friend[i]
        travel_time_expr = 0
        for p in range(5):
            for c in range(5):
                cond = And(prev_friend == p, current_friend == c)
                travel_time_expr += If(cond, travel_time_between_friends[p][c], 0)
        s.add(arrival_i == end[i-1] + travel_time_expr)

    # Ensure start_i >= arrival_i
    s.add(Implies(met_i, start_i >= arrival_i))

# Ensure no two steps meet the same friend
for i in range(5):
    for j in range(i+1, 5):
        s.add(Not(And(met[i], met[j], friend[i] == friend[j])))

# Objective: maximize the number of friends met
objective = Sum([If(met[i], 1, 0) for i in range(5)])
s.maximize(objective)

# Check for solution
if s.check() == sat:
    model = s.model()
    itinerary = []
    for i in range(5):
        if is_true(model.eval(met[i])):
            friend_idx = model.eval(friend[i]).as_long()
            start_time = model.eval(start[i]).as_long()
            end_time = model.eval(end[i]).as_long()
            name = friends_data[friend_idx]['name']
            location = friends_locations[friend_idx]
            def to_time_str(minutes):
                hours = minutes // 60
                mins = minutes % 60
                return f"{hours}:{mins:02d}"
            start_str = to_time_str(start_time)
            end_str = to_time_str(end_time)
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": name,
                "start_time": start_str,
                "end_time": end_str
            })
    print(json.dumps({"itinerary": itinerary}))
else:
    print(json.dumps({"itinerary": []}))