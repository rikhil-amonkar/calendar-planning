from z3 import *
import json

def to_time_str(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

friends = [
    {'location': 'Golden Gate Park', 'available_start': 480, 'available_end': 810, 'duration': 15},
    {'location': 'Russian Hill', 'available_start': 540, 'available_end': 1020, 'duration': 30},
    {'location': 'Alamo Square', 'available_start': 1080, 'available_end': 1245, 'duration': 90},
    {'location': 'Mission District', 'available_start': 1230, 'available_end': 1320, 'duration': 90},
]

travel_time_matrix = [
    [0, 19, 10, 17],
    [21, 0, 15, 16],
    [9, 13, 0, 10],
    [17, 15, 11, 0],
]

sunset_to_friend = [11, 24, 17, 24]

solver = Solver()

friends_order = [Int(f"friend_{i}") for i in range(4)]
solver.add(Distinct(friends_order))
for f in friends_order:
    solver.add(And(0 <= f, f <= 3))

start = [Int(f"start_{i}") for i in range(4)]
end = [Int(f"end_{i}") for i in range(4)]

prev_end = 540  # 9:00 AM in minutes

for i in range(4):
    if i == 0:
        travel_time = If(friends_order[0] == 0, 11,
                         If(friends_order[0] == 1, 24,
                            If(friends_order[0] == 2, 17, 24)))
    else:
        prev_friend = friends_order[i-1]
        current_friend = friends_order[i]
        travel_time = If(prev_friend == 0,
                         If(current_friend == 0, 0,
                            If(current_friend == 1, 19,
                               If(current_friend == 2, 10, 17))),
                         If(prev_friend == 1,
                            If(current_friend == 0, 21,
                               If(current_friend == 1, 0,
                                  If(current_friend == 2, 15, 16))),
                            If(prev_friend == 2,
                               If(current_friend == 0, 9,
                                  If(current_friend == 1, 13,
                                     If(current_friend == 2, 0, 10))),
                               If(current_friend == 0, 17,
                                  If(current_friend == 1, 15,
                                     If(current_friend == 2, 11, 0)))))
    arrival_time = prev_end + travel_time
    solver.add(start[i] >= arrival_time)
    friend_idx = friends_order[i]
    duration = friends[friend_idx]['duration']
    solver.add(end[i] == start[i] + duration)
    available_start = friends[friend_idx]['available_start']
    solver.add(start[i] >= available_start)
    available_end = friends[friend_idx]['available_end']
    solver.add(end[i] <= available_end)
    prev_end = end[i]

if solver.check() == sat:
    model = solver.model()
    order = [model.eval(friends_order[i]).as_long() for i in range(4)]
    starts = [model.eval(start[i]).as_long() for i in range(4)]
    ends = [model.eval(end[i]).as_long() for i in range(4)]
    itinerary = []
    for i in range(4):
        friend_idx = order[i]
        loc = friends[friend_idx]['location']
        person = ['Daniel', 'Margaret', 'Charles', 'Stephanie'][friend_idx]
        itinerary.append({
            "action": "meet",
            "location": loc,
            "person": person,
            "start_time": to_time_str(starts[i]),
            "end_time": to_time_str(ends[i])
        })
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found")