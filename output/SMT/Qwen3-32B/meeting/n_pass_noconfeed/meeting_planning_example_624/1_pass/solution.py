from z3 import *
import json

def location_name(loc):
    if loc == 1:
        return "Haight-Ashbury"
    elif loc == 2:
        return "Fisherman's Wharf"
    elif loc == 3:
        return "The Castro"
    elif loc == 4:
        return "Chinatown"
    elif loc == 5:
        return "Alamo Square"
    elif loc == 6:
        return "North Beach"
    elif loc == 7:
        return "Russian Hill"
    else:
        return "Unknown"

def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def build_travel_time_expr(loc_prev, loc_curr):
    curr_expr_1 = If(loc_curr == 1, 0, 
                     If(loc_curr == 2, 23, 
                     If(loc_curr == 3, 6, 
                     If(loc_curr == 4, 19, 
                     If(loc_curr == 5, 5, 
                     If(loc_curr == 6, 19, 
                     If(loc_curr == 7, 17, 0))))))
    curr_expr_2 = If(loc_curr == 1, 22, 
                     If(loc_curr == 2, 0, 
                     If(loc_curr == 3, 24, 
                     If(loc_curr == 4, 12, 
                     If(loc_curr == 5, 20, 
                     If(loc_curr == 6, 6, 
                     If(loc_curr == 7, 7, 0))))))
    curr_expr_3 = If(loc_curr == 1, 6, 
                     If(loc_curr == 2, 24, 
                     If(loc_curr == 3, 0, 
                     If(loc_curr == 4, 20, 
                     If(loc_curr == 5, 8, 
                     If(loc_curr == 6, 20, 
                     If(loc_curr == 7, 18, 0))))))
    curr_expr_4 = If(loc_curr == 1, 19, 
                     If(loc_curr == 2, 8, 
                     If(loc_curr == 3, 22, 
                     If(loc_curr == 4, 0, 
                     If(loc_curr == 5, 17, 
                     If(loc_curr == 6, 3, 
                     If(loc_curr == 7, 7, 0))))))
    curr_expr_5 = If(loc_curr == 1, 5, 
                     If(loc_curr == 2, 19, 
                     If(loc_curr == 3, 8, 
                     If(loc_curr == 4, 16, 
                     If(loc_curr == 5, 0, 
                     If(loc_curr == 6, 15, 
                     If(loc_curr == 7, 13, 0))))))
    curr_expr_6 = If(loc_curr == 1, 18, 
                     If(loc_curr == 2, 6, 
                     If(loc_curr == 3, 22, 
                     If(loc_curr == 4, 16, 
                     If(loc_curr == 5, 0, 
                     If(loc_curr == 6, 4, 
                     If(loc_curr == 7, 5, 0))))))
    curr_expr_7 = If(loc_curr == 1, 17, 
                     If(loc_curr == 2, 7, 
                     If(loc_curr == 3, 21, 
                     If(loc_curr == 4, 9, 
                     If(loc_curr == 5, 15, 
                     If(loc_curr == 6, 5, 
                     If(loc_curr == 7, 0, 0))))))
    expr = If(loc_prev == 1, curr_expr_1,
              If(loc_prev == 2, curr_expr_2,
              If(loc_prev == 3, curr_expr_3,
              If(loc_prev == 4, curr_expr_4,
              If(loc_prev == 5, curr_expr_5,
              If(loc_prev == 6, curr_expr_6,
              If(loc_prev == 7, curr_expr_7, 0)))))))
    return expr

friends = [
    {
        'name': 'Carol',
        'location': 1,
        'available_start': 21 * 60 + 30,
        'available_end': 22 * 60 + 30,
        'duration': 60
    },
    {
        'name': 'Laura',
        'location': 2,
        'available_start': 11 * 60 + 45,
        'available_end': 21 * 60 + 30,
        'duration': 60
    },
    {
        'name': 'Karen',
        'location': 3,
        'available_start': 7 * 60 + 15,
        'available_end': 14 * 60 + 0,
        'duration': 75
    },
    {
        'name': 'Elizabeth',
        'location': 4,
        'available_start': 12 * 60 + 15,
        'available_end': 21 * 60 + 30,
        'duration': 75
    },
    {
        'name': 'Deborah',
        'location': 5,
        'available_start': 12 * 60 + 0,
        'available_end': 15 * 60 + 0,
        'duration': 105
    },
    {
        'name': 'Jason',
        'location': 6,
        'available_start': 14 * 60 + 45,
        'available_end': 19 * 60 + 0,
        'duration': 90
    },
    {
        'name': 'Steven',
        'location': 7,
        'available_start': 14 * 60 + 45,
        'available_end': 18 * 60 + 30,
        'duration': 120
    }
]

travel_time = [
    [0, 7, 24, 13, 23, 10, 24, 19],
    [7, 0, 23, 6, 19, 5, 19, 17],
    [25, 22, 0, 26, 12, 20, 6, 7],
    [11, 6, 24, 0, 20, 8, 20, 18],
    [23, 19, 8, 22, 0, 17, 3, 7],
    [9, 5, 19, 8, 16, 0, 15, 13],
    [22, 18, 5, 22, 6, 16, 0, 4],
    [21, 17, 7, 21, 9, 15, 5, 0]
]

solver = Optimize()

loc = [Int(f'loc_{i}') for i in range(7)]
start = [Int(f'start_{i}') for i in range(7)]
used = [Bool(f'used_{i}') for i in range(7)]

for i in range(1, 7):
    solver.add(Implies(used[i], used[i-1]))

for i in range(7):
    solver.add(Implies(used[i], And(1 <= loc[i], loc[i] <= 7)))

available_start = []
available_end = []
durations = []

for i in range(7):
    as_i = If(loc[i] == 1, friends[0]['available_start'],
              If(loc[i] == 2, friends[1]['available_start'],
              If(loc[i] == 3, friends[2]['available_start'],
              If(loc[i] == 4, friends[3]['available_start'],
              If(loc[i] == 5, friends[4]['available_start'],
              If(loc[i] == 6, friends[5]['available_start'],
              If(loc[i] == 7, friends[6]['available_start'], 0))))))
    available_start.append(as_i)

    ae_i = If(loc[i] == 1, friends[0]['available_end'],
              If(loc[i] == 2, friends[1]['available_end'],
              If(loc[i] == 3, friends[2]['available_end'],
              If(loc[i] == 4, friends[3]['available_end'],
              If(loc[i] == 5, friends[4]['available_end'],
              If(loc[i] == 6, friends[5]['available_end'],
              If(loc[i] == 7, friends[6]['available_end'], 0))))))
    available_end.append(ae_i)

    dur_i = If(loc[i] == 1, friends[0]['duration'],
               If(loc[i] == 2, friends[1]['duration'],
               If(loc[i] == 3, friends[2]['duration'],
               If(loc[i] == 4, friends[3]['duration'],
               If(loc[i] == 5, friends[4]['duration'],
               If(loc[i] == 6, friends[5]['duration'],
               If(loc[i] == 7, friends[6]['duration'], 0))))))
    durations.append(dur_i)

for i in range(7):
    solver.add(Implies(used[i], start[i] >= available_start[i]))
    solver.add(Implies(used[i], start[i] + durations[i] <= available_end[i]))

solver.add(Implies(used[0], start[0] >= 540 + travel_time[0][loc[0]]))

for i in range(1, 7):
    tt_prev = build_travel_time_expr(loc[i-1], loc[i])
    constraint = Implies(used[i], start[i] >= start[i-1] + durations[i-1] + tt_prev)
    solver.add(constraint)

for i in range(7):
    for j in range(i+1, 7):
        solver.add(Implies(And(used[i], used[j]), loc[i] != loc[j]))

solver.maximize(Sum([If(used[i], 1, 0) for i in range(7)]))

if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for i in range(7):
        if is_true(model.eval(used[i])):
            l = model.eval(loc[i]).as_long()
            s = model.eval(start[i]).as_long()
            for friend in friends:
                if friend['location'] == l:
                    friend_name = friend['name']
                    break
            dur = model.eval(durations[i]).as_long()
            end_time = s + dur
            start_time_str = format_time(s)
            end_time_str = format_time(end_time)
            itinerary.append({
                "action": "meet",
                "location": location_name(l),
                "person": friend_name,
                "start_time": start_time_str,
                "end_time": end_time_str
            })
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print(json.dumps({"itinerary": []}, indent=2))