from z3 import *
import json

def get_location(friend_idx):
    return If(friend_idx == 0, 1,
              If(friend_idx == 1, 2,
                 If(friend_idx == 2, 3, 4)))

def get_available_start(friend_idx):
    return If(friend_idx == 0, 1050,
              If(friend_idx == 1, 495,
                 If(friend_idx == 2, 630, 540)))

def get_available_end(friend_idx):
    return If(friend_idx == 0, 1245,
              If(friend_idx == 1, 720,
                 If(friend_idx == 2, 1125, 765)))

def get_duration(friend_idx):
    return If(friend_idx == 0, 105,
              If(friend_idx == 1, 15,
                 If(friend_idx == 2, 30, 30)))

def get_travel_time(prev_loc, current_loc):
    return If(prev_loc == 0,
              If(current_loc == 0, 0,
                 If(current_loc == 1, 24,
                    If(current_loc == 2, 30,
                       If(current_loc == 3, 16, 29)))),
              If(prev_loc == 1,
                 If(current_loc == 0, 23,
                    If(current_loc == 1, 0,
                       If(current_loc == 2, 9,
                          If(current_loc == 3, 14, 7)))),
                 If(prev_loc == 2,
                    If(current_loc == 0, 29,
                       If(current_loc == 1, 7,
                          If(current_loc == 2, 0,
                             If(current_loc == 3, 19, 8)))),
                    If(prev_loc == 3,
                       If(current_loc == 0, 15,
                          If(current_loc == 1, 14,
                             If(current_loc == 2, 21,
                                If(current_loc == 3, 0, 19)))),
                       If(prev_loc == 4,
                          If(current_loc == 0, 27,
                             If(current_loc == 1, 7,
                                If(current_loc == 2, 12,
                                   If(current_loc == 3, 17, 0)))),
                          0))))) 

solver = Solver()

friends = [Int(f'friend_{i}') for i in range(4)]
starts = [Int(f'start_{i}') for i in range(4)]
ends = [Int(f'end_{i}') for i in range(4)]

for f in friends:
    solver.add(And(f >= 0, f <= 3))
solver.add(Distinct(friends))

for i in range(4):
    loc_i = get_location(friends[i])
    available_start_i = get_available_start(friends[i])
    available_end_i = get_available_end(friends[i])
    duration_i = get_duration(friends[i])
    solver.add(starts[i] >= available_start_i)
    solver.add(ends[i] <= available_end_i)
    solver.add(ends[i] == starts[i] + duration_i)

loc_0 = get_location(friends[0])
travel_time_0 = get_travel_time(0, loc_0)
solver.add(starts[0] >= 540 + travel_time_0)

for i in range(1, 4):
    prev_loc = get_location(friends[i-1])
    current_loc = get_location(friends[i])
    travel_time_i = get_travel_time(prev_loc, current_loc)
    solver.add(starts[i] >= ends[i-1] + travel_time_i)

if solver.check() == sat:
    model = solver.model()
    friends_vals = [model.evaluate(friends[i]).as_long() for i in range(4)]
    starts_vals = [model.evaluate(starts[i]).as_long() for i in range(4)]
    ends_vals = [model.evaluate(ends[i]).as_long() for i in range(4)]
    
    friends_names = ['William', 'Michelle', 'George', 'Robert']
    itinerary = []
    for i in range(4):
        person_idx = friends_vals[i]
        person_name = friends_names[person_idx]
        start_time = starts_vals[i]
        end_time = ends_vals[i]
        def format_time(m):
            h = m // 60
            m2 = m % 60
            return f"{h:02d}:{m2:02d}"
        itinerary.append({
            "action": "meet",
            "person": person_name,
            "start_time": format_time(start_time),
            "end_time": format_time(end_time)
        })
    print(json.dumps({"itinerary": itinerary}))
else:
    print("No solution found")