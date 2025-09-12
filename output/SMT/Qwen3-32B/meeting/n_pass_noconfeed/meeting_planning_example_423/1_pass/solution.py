from z3 import *

def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

friends_data = [
    None,
    {
        'name': 'Brian',
        'location': 3,
        'available_start': 585,  # 9:45 AM
        'available_end': 1305,   # 9:45 PM
        'required_duration': 15
    },
    {
        'name': 'Elizabeth',
        'location': 4,
        'available_start': 525,  # 8:45 AM
        'available_end': 1290,   # 9:30 PM
        'required_duration': 105
    },
    {
        'name': 'Jason',
        'location': 1,
        'available_start': 780,  # 1:00 PM
        'available_end': 1245,   # 8:45 PM
        'required_duration': 90
    },
    {
        'name': 'Melissa',
        'location': 2,
        'available_start': 1125, # 6:45 PM
        'available_end': 1215,   # 8:15 PM
        'required_duration': 45
    },
    {
        'name': 'Laura',
        'location': 5,
        'available_start': 855,  # 2:15 PM
        'available_end': 1170,   # 7:30 PM
        'required_duration': 75
    }
]

travel_times = [
    [0, 7, 18, 23, 12, 22],     # Presidio
    [7, 0, 17, 22, 9, 21],      # Richmond District
    [17, 18, 0, 8, 22, 7],      # North Beach
    [22, 21, 7, 0, 23, 9],      # Financial District
    [11, 7, 24, 26, 0, 22],     # Golden Gate Park
    [24, 20, 10, 9, 22, 0]      # Union Square
]

s = Optimize()

friends = [Int(f'friend_{i}') for i in range(1, 6)]
current_times = [Int(f'current_time_{i}') for i in range(1, 6)]
current_locations = [Int(f'current_location_{i}') for i in range(1, 6)]

for f in friends:
    s.add(And(f >= 0, f <= 5))

# Step 1
prev_time = 540
prev_loc = 0
friend = friends[0]
loc_expr_1 = If(friend == 1, 3,
         If(friend == 2, 4,
            If(friend == 3, 1,
               If(friend == 4, 2,
                  If(friend == 5, 5, 0)))))
travel_time_expr_1 = If(friend == 1, travel_times[prev_loc][3],
                        If(friend == 2, travel_times[prev_loc][4],
                           If(friend == 3, travel_times[prev_loc][1],
                              If(friend == 4, travel_times[prev_loc][2],
                                 If(friend == 5, travel_times[prev_loc][5], 0)))))
arrival_time_1 = prev_time + travel_time_expr_1
available_start_expr_1 = If(friend == 1, friends_data[1]['available_start'],
                            If(friend == 2, friends_data[2]['available_start'],
                               If(friend == 3, friends_data[3]['available_start'],
                                  If(friend == 4, friends_data[4]['available_start'],
                                     If(friend == 5, friends_data[5]['available_start'], 0))))
available_end_expr_1 = If(friend == 1, friends_data[1]['available_end'],
                          If(friend == 2, friends_data[2]['available_end'],
                             If(friend == 3, friends_data[3]['available_end'],
                                If(friend == 4, friends_data[4]['available_end'],
                                   If(friend == 5, friends_data[5]['available_end'], 0))))
required_duration_expr_1 = If(friend == 1, friends_data[1]['required_duration'],
                              If(friend == 2, friends_data[2]['required_duration'],
                                 If(friend == 3, friends_data[3]['required_duration'],
                                    If(friend == 4, friends_data[4]['required_duration'],
                                       If(friend == 5, friends_data[5]['required_duration'], 0))))
s.add(Implies(friend != 0, arrival_time_1 >= available_start_expr_1))
s.add(Implies(friend != 0, arrival_time_1 + required_duration_expr_1 <= available_end_expr_1))
current_time_1_expr = If(friend != 0, arrival_time_1 + required_duration_expr_1, prev_time)
s.add(current_times[0] == current_time_1_expr)
current_location_1_expr = If(friend != 0, loc_expr_1, prev_loc)
s.add(current_locations[0] == current_location_1_expr)

# Step 2
prev_time = current_times[0]
prev_loc = current_locations[0]
friend = friends[1]
loc_expr_2 = If(friend == 1, 3,
         If(friend == 2, 4,
            If(friend == 3, 1,
               If(friend == 4, 2,
                  If(friend == 5, 5, 0)))))
travel_time_expr_2 = If(friend == 1, travel_times[prev_loc][3],
                        If(friend == 2, travel_times[prev_loc][4],
                           If(friend == 3, travel_times[prev_loc][1],
                              If(friend == 4, travel_times[prev_loc][2],
                                 If(friend == 5, travel_times[prev_loc][5], 0)))))
arrival_time_2 = prev_time + travel_time_expr_2
available_start_expr_2 = If(friend == 1, friends_data[1]['available_start'],
                            If(friend == 2, friends_data[2]['available_start'],
                               If(friend == 3, friends_data[3]['available_start'],
                                  If(friend == 4, friends_data[4]['available_start'],
                                     If(friend == 5, friends_data[5]['available_start'], 0))))
available_end_expr_2 = If(friend == 1, friends_data[1]['available_end'],
                          If(friend == 2, friends_data[2]['available_end'],
                             If(friend == 3, friends_data[3]['available_end'],
                                If(friend == 4, friends_data[4]['available_end'],
                                   If(friend == 5, friends_data[5]['available_end'], 0))))
required_duration_expr_2 = If(friend == 1, friends_data[1]['required_duration'],
                              If(friend == 2, friends_data[2]['required_duration'],
                                 If(friend == 3, friends_data[3]['required_duration'],
                                    If(friend == 4, friends_data[4]['required_duration'],
                                       If(friend == 5, friends_data[5]['required_duration'], 0))))
s.add(Implies(friend != 0, arrival_time_2 >= available_start_expr_2))
s.add(Implies(friend != 0, arrival_time_2 + required_duration_expr_2 <= available_end_expr_2))
current_time_2_expr = If(friend != 0, arrival_time_2 + required_duration_expr_2, prev_time)
s.add(current_times[1] == current_time_2_expr)
current_location_2_expr = If(friend != 0, loc_expr_2, prev_loc)
s.add(current_locations[1] == current_location_2_expr)

# Step 3
prev_time = current_times[1]
prev_loc = current_locations[1]
friend = friends[2]
loc_expr_3 = If(friend == 1, 3,
         If(friend == 2, 4,
            If(friend == 3, 1,
               If(friend == 4, 2,
                  If(friend == 5, 5, 0)))))
travel_time_expr_3 = If(friend == 1, travel_times[prev_loc][3],
                        If(friend == 2, travel_times[prev_loc][4],
                           If(friend == 3, travel_times[prev_loc][1],
                              If(friend == 4, travel_times[prev_loc][2],
                                 If(friend == 5, travel_times[prev_loc][5], 0)))))
arrival_time_3 = prev_time + travel_time_expr_3
available_start_expr_3 = If(friend == 1, friends_data[1]['available_start'],
                            If(friend == 2, friends_data[2]['available_start'],
                               If(friend == 3, friends_data[3]['available_start'],
                                  If(friend == 4, friends_data[4]['available_start'],
                                     If(friend == 5, friends_data[5]['available_start'], 0))))
available_end_expr_3 = If(friend == 1, friends_data[1]['available_end'],
                          If(friend == 2, friends_data[2]['available_end'],
                             If(friend == 3, friends_data[3]['available_end'],
                                If(friend == 4, friends_data[4]['available_end'],
                                   If(friend == 5, friends_data[5]['available_end'], 0))))
required_duration_expr_3 = If(friend == 1, friends_data[1]['required_duration'],
                              If(friend == 2, friends_data[2]['required_duration'],
                                 If(friend == 3, friends_data[3]['required_duration'],
                                    If(friend == 4, friends_data[4]['required_duration'],
                                       If(friend == 5, friends_data[5]['required_duration'], 0))))
s.add(Implies(friend != 0, arrival_time_3 >= available_start_expr_3))
s.add(Implies(friend != 0, arrival_time_3 + required_duration_expr_3 <= available_end_expr_3))
current_time_3_expr = If(friend != 0, arrival_time_3 + required_duration_expr_3, prev_time)
s.add(current_times[2] == current_time_3_expr)
current_location_3_expr = If(friend != 0, loc_expr_3, prev_loc)
s.add(current_locations[2] == current_location_3_expr)

# Step 4
prev_time = current_times[2]
prev_loc = current_locations[2]
friend = friends[3]
loc_expr_4 = If(friend == 1, 3,
         If(friend == 2, 4,
            If(friend == 3, 1,
               If(friend == 4, 2,
                  If(friend == 5, 5, 0)))))
travel_time_expr_4 = If(friend == 1, travel_times[prev_loc][3],
                        If(friend == 2, travel_times[prev_loc][4],
                           If(friend == 3, travel_times[prev_loc][1],
                              If(friend == 4, travel_times[prev_loc][2],
                                 If(friend == 5, travel_times[prev_loc][5], 0)))))
arrival_time_4 = prev_time + travel_time_expr_4
available_start_expr_4 = If(friend == 1, friends_data[1]['available_start'],
                            If(friend == 2, friends_data[2]['available_start'],
                               If(friend == 3, friends_data[3]['available_start'],
                                  If(friend == 4, friends_data[4]['available_start'],
                                     If(friend == 5, friends_data[5]['available_start'], 0))))
available_end_expr_4 = If(friend == 1, friends_data[1]['available_end'],
                          If(friend == 2, friends_data[2]['available_end'],
                             If(friend == 3, friends_data[3]['available_end'],
                                If(friend == 4, friends_data[4]['available_end'],
                                   If(friend == 5, friends_data[5]['available_end'], 0))))
required_duration_expr_4 = If(friend == 1, friends_data[1]['required_duration'],
                              If(friend == 2, friends_data[2]['required_duration'],
                                 If(friend == 3, friends_data[3]['required_duration'],
                                    If(friend == 4, friends_data[4]['required_duration'],
                                       If(friend == 5, friends_data[5]['required_duration'], 0))))
s.add(Implies(friend != 0, arrival_time_4 >= available_start_expr_4))
s.add(Implies(friend != 0, arrival_time_4 + required_duration_expr_4 <= available_end_expr_4))
current_time_4_expr = If(friend != 0, arrival_time_4 + required_duration_expr_4, prev_time)
s.add(current_times[3] == current_time_4_expr)
current_location_4_expr = If(friend != 0, loc_expr_4, prev_loc)
s.add(current_locations[3] == current_location_4_expr)

# Step 5
prev_time = current_times[3]
prev_loc = current_locations[3]
friend = friends[4]
loc_expr_5 = If(friend == 1, 3,
         If(friend == 2, 4,
            If(friend == 3, 1,
               If(friend == 4, 2,
                  If(friend == 5, 5, 0)))))
travel_time_expr_5 = If(friend == 1, travel_times[prev_loc][3],
                        If(friend == 2, travel_times[prev_loc][4],
                           If(friend == 3, travel_times[prev_loc][1],
                              If(friend == 4, travel_times[prev_loc][2],
                                 If(friend == 5, travel_times[prev_loc][5], 0)))))
arrival_time_5 = prev_time + travel_time_expr_5
available_start_expr_5 = If(friend == 1, friends_data[1]['available_start'],
                            If(friend == 2, friends_data[2]['available_start'],
                               If(friend == 3, friends_data[3]['available_start'],
                                  If(friend == 4, friends_data[4]['available_start'],
                                     If(friend == 5, friends_data[5]['available_start'], 0))))
available_end_expr_5 = If(friend == 1, friends_data[1]['available_end'],
                          If(friend == 2, friends_data[2]['available_end'],
                             If(friend == 3, friends_data[3]['available_end'],
                                If(friend == 4, friends_data[4]['available_end'],
                                   If(friend == 5, friends_data[5]['available_end'], 0))))
required_duration_expr_5 = If(friend == 1, friends_data[1]['required_duration'],
                              If(friend == 2, friends_data[2]['required_duration'],
                                 If(friend == 3, friends_data[3]['required_duration'],
                                    If(friend == 4, friends_data[4]['required_duration'],
                                       If(friend == 5, friends_data[5]['required_duration'], 0))))
s.add(Implies(friend != 0, arrival_time_5 >= available_start_expr_5))
s.add(Implies(friend != 0, arrival_time_5 + required_duration_expr_5 <= available_end_expr_5))
current_time_5_expr = If(friend != 0, arrival_time_5 + required_duration_expr_5, prev_time)
s.add(current_times[4] == current_time_5_expr)
current_location_5_expr = If(friend != 0, loc_expr_5, prev_loc)
s.add(current_locations[4] == current_location_5_expr)

num_friends_met = Sum([If(f != 0, 1, 0) for f in friends])
s.maximize(num_friends_met)

if s.check() == sat:
    model = s.model()
    meetings = []
    current_time = 540
    current_location = 0
    for i in range(5):
        friend_val = model.eval(friends[i]).as_long()
        if friend_val != 0:
            friend_info = friends_data[friend_val]
            loc = friend_info['location']
            travel_time = travel_times[current_location][loc]
            arrival_time = current_time + travel_time
            required_duration = friend_info['required_duration']
            end_time = arrival_time + required_duration
            meetings.append({
                "action": "meet",
                "location": friends_data[friend_val]['name'],
                "person": friends_data[friend_val]['name'],
                "start_time": to_time_str(arrival_time),
                "end_time": to_time_str(end_time)
            })
            current_time = end_time
            current_location = loc
    print(json.dumps({"itinerary": meetings}))
else:
    print(json.dumps({"itinerary": []}))