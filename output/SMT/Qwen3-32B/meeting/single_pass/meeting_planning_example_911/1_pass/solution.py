from z3 import *

def main():
    # Convert all times to minutes since midnight
    friends_data = [
        {
            'name': 'Nancy',
            'available_start': 8*60 + 15,  # 8:15 AM
            'available_end': 12*60 + 45,   # 12:45 PM
            'duration': 90,
        },
        {
            'name': 'Stephanie',
            'available_start': 10*60 + 15, # 10:15 AM
            'available_end': 12*60 + 15,   # 12:15 PM
            'duration': 75,
        },
        {
            'name': 'David',
            'available_start': 11*60 + 15, # 11:15 AM
            'available_end': 13*60 + 15,   # 1:15 PM
            'duration': 120,
        },
        {
            'name': 'Melissa',
            'available_start': 14*60 + 0,  # 2:00 PM
            'available_end': 19*60 + 30,   # 7:30 PM
            'duration': 30,
        },
        {
            'name': 'Brian',
            'available_start': 14*60 + 15, # 2:15 PM
            'available_end': 16*60 + 0,    # 4:00 PM
            'duration': 105,
        },
        {
            'name': 'Sarah',
            'available_start': 17*60 + 0,  # 5:00 PM
            'available_end': 19*60 + 15,   # 7:15 PM
            'duration': 75,
        },
        {
            'name': 'Steven',
            'available_start': 17*60 + 30, # 5:30 PM
            'available_end': 20*60 + 30,   # 8:30 PM
            'duration': 15,
        },
        {
            'name': 'James',
            'available_start': 15*60 + 0,  # 3:00 PM
            'available_end': 18*60 + 15,   # 6:15 PM
            'duration': 120,
        },
        {
            'name': 'Elizabeth',
            'available_start': 11*60 + 30, # 11:30 AM
            'available_end': 21*60 + 0,    # 9:00 PM
            'duration': 60,
        },
        {
            'name': 'Robert',
            'available_start': 13*60 + 15, # 1:15 PM
            'available_end': 15*60 + 15,   # 3:15 PM
            'duration': 45,
        },
    ]

    # Define travel time matrix (indices 0-10 correspond to locations)
    travel_time = {
        0: {1:20, 2:11, 3:22, 4:6, 5:16, 6:16, 7:21, 8:20, 9:19, 10:21},
        1: {0:23, 2:22, 3:6, 4:18, 5:18, 6:7, 7:9, 8:17, 9:7, 10:8},
        2: {0:13, 1:23, 3:25, 4:7, 5:7, 6:20, 7:16, 8:11, 9:22, 10:26},
        3: {0:25, 1:5, 2:25, 4:21, 5:21, 6:10, 7:12, 8:20, 9:10, 10:5},
        4: {0:6, 1:19, 2:7, 3:20, 5:10, 6:15, 7:17, 8:15, 9:19, 10:21},
        5: {0:16, 1:17, 2:9, 3:19, 4:10, 6:17, 7:9, 8:7, 9:21, 10:22},
        6: {0:17, 1:8, 2:17, 3:9, 4:13, 5:14, 7:11, 8:18, 9:22, 10:9},
        7: {0:22, 1:11, 2:18, 3:14, 4:16, 5:11, 6:12, 8:10, 9:16, 10:17},
        8: {0:21, 1:18, 2:12, 3:20, 4:15, 5:7, 6:18, 7:11, 9:22, 10:23},
        9: {0:17, 1:10, 2:22, 3:11, 4:18, 5:20, 6:9, 7:18, 8:24, 10:9},
        10: {0:20, 1:7, 2:23, 3:4, 4:19, 5:21, 6:8, 7:15, 8:22, 9:9},
    }

    s = Optimize()

    friends = [Int('friend_%d' % i) for i in range(10)]
    starts = [Int('start_%d' % i) for i in range(10)]
    ends = [Int('end_%d' % i) for i in range(10)]

    # Add constraints for friends to be in range 0-9
    for f in friends:
        s.add(And(f >= 0, f <= 9))

    # Helper to get location for a friend index
    def get_loc(friend_idx):
        return If(friend_idx == 0, 6,
                  If(friend_idx == 1, 4,
                     If(friend_idx == 2, 7,
                        If(friend_idx == 3, 5,
                           If(friend_idx == 4, 3,
                              If(friend_idx == 5, 2,
                                 If(friend_idx == 6, 1,
                                    If(friend_idx == 7, 8,
                                       If(friend_idx == 8, 9,
                                          If(friend_idx == 9, 10, 0)
                                          )
                                       )
                                    )
                                 )
                              )
                           )
                        )
                     )
                  )

    for i in range(10):
        f = friends[i]
        loc_i = get_loc(f)
        start = starts[i]
        end = ends[i]
        duration = friends_data[f]['duration']
        available_start = friends_data[f]['available_start']
        available_end = friends_data[f]['available_end']

        if i == 0:
            arrival_time = 540 + travel_time[0][loc_i]
        else:
            prev_loc = get_loc(friends[i-1])
            arrival_time = ends[i-1] + travel_time[prev_loc][loc_i]

        s.add(start >= arrival_time)
        s.add(start >= available_start)
        s.add(end == start + duration)
        s.add(end <= available_end)

    # Ensure each friend is visited at most once
    for i in range(10):
        for j in range(i+1, 10):
            s.add(friends[i] != friends[j])

    # Maximize the number of friends
    used = [Bool('used_%d' % f) for f in range(10)]
    for f in range(10):
        used_expr = False
        for i in range(10):
            used_expr = Or(used_expr, friends[i] == f)
        s.add(used[f] == used_expr)
    s.maximize(Sum([If(used[f], 1, 0) for f in range(10)]))

    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(10):
            f_val = model.eval(friends[i])
            start_val = model.eval(starts[i])
            end_val = model.eval(ends[i])
            if f_val >= 0 and f_val <= 9:
                friend_index = f_val.as_long()
                name = friends_data[friend_index]['name']
                start_time = start_val.as_long()
                end_time = end_val.as_long()
                start_hh = start_time // 60
                start_mm = start_time % 60
                end_hh = end_time // 60
                end_mm = end_time % 60
                start_str = f"{start_hh:02d}:{start_mm:02d}"
                end_str = f"{end_hh:02d}:{end_mm:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": start_str,
                    "end_time": end_str
                })
        # Sort by start time
        itinerary.sort(key=lambda x: x['start_time'])
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

if __name__ == "__main__":
    solution = main()
    import json
    print(json.dumps(solution))