import json
from z3 import *

districts = [
    "Russian Hill",          #0
    "Marina District",       #1
    "Financial District",    #2
    "Alamo Square",          #3
    "Golden Gate Park",      #4
    "The Castro",            #5
    "Bayview",               #6
    "Sunset District",       #7
    "Haight-Ashbury",        #8
    "Nob Hill"               #9
]

travel_time = [
    [0, 7, 11, 15, 21, 21, 23, 23, 17, 5],
    [8, 0, 17, 15, 18, 22, 27, 19, 16, 12],
    [11, 15, 0, 17, 23, 20, 19, 30, 19, 8],
    [13, 15, 17, 0, 9, 8, 16, 16, 5, 11],
    [19, 16, 26, 9, 0, 13, 23, 10, 7, 20],
    [18, 21, 21, 8, 11, 0, 19, 17, 6, 16],
    [23, 27, 19, 16, 22, 19, 0, 23, 19, 20],
    [24, 21, 30, 17, 11, 17, 22, 0, 15, 27],
    [17, 17, 21, 5, 7, 6, 18, 15, 0, 15],
    [5, 11, 9, 11, 17, 17, 19, 24, 13, 0]
]

friend_data = [None] * 10
friend_data[1] = {'start': 585, 'end': 720, 'duration': 90, 'name': 'Mark'}
friend_data[2] = {'start': 30, 'end': 225, 'duration': 90, 'name': 'Karen'}
friend_data[3] = {'start': 60, 'end': 630, 'duration': 90, 'name': 'Barbara'}
friend_data[4] = {'start': 465, 'end': 660, 'duration': 105, 'name': 'Nancy'}
friend_data[5] = {'start': 0, 'end': 540, 'duration': 120, 'name': 'David'}
friend_data[6] = {'start': 555, 'end': 645, 'duration': 45, 'name': 'Linda'}
friend_data[7] = {'start': 60, 'end': 525, 'duration': 120, 'name': 'Kevin'}
friend_data[8] = {'start': 75, 'end': 390, 'duration': 45, 'name': 'Matthew'}
friend_data[9] = {'start': 165, 'end': 465, 'duration': 105, 'name': 'Andrew'}

s = [Int(f's_{i}') for i in range(10)]
e = [Int(f'e_{i}') for i in range(10)]
m = [Bool(f'm_{i}') for i in range(10)]

solver = Solver()

solver.add(s[0] == 0)
solver.add(e[0] == 0)
solver.add(m[0] == True)

for i in range(1, 10):
    solver.add(Implies(m[i], s[i] >= friend_data[i]['start']))
    solver.add(Implies(m[i], e[i] == s[i] + friend_data[i]['duration']))
    solver.add(Implies(m[i], e[i] <= friend_data[i]['end']))

for i in range(0, 10):
    for j in range(i+1, 10):
        disj = Or(
            s[j] >= e[i] + travel_time[i][j],
            s[i] >= e[j] + travel_time[j][i]
        )
        solver.add(Implies(And(m[i], m[j]), disj))

opt = Optimize()
for c in solver.assertions():
    opt.add(c)

objective = Sum([If(m[i], 1, 0) for i in range(1,10)])
opt.maximize(objective)

itinerary_list = []
if opt.check() == sat:
    model = opt.model()
    for i in range(1, 10):
        if model.evaluate(m[i]):
            start_val = model.evaluate(s[i])
            start_min = start_val.as_long() if is_int_value(start_val) else int(str(start_val))
            duration = friend_data[i]['duration']
            end_min = start_min + duration
            total_minutes_start = start_min
            hours_start = 9 + total_minutes_start // 60
            minutes_start = total_minutes_start % 60
            start_str = f"{hours_start:02d}:{minutes_start:02d}"
            total_minutes_end = end_min
            hours_end = 9 + total_minutes_end // 60
            minutes_end = total_minutes_end % 60
            end_str = f"{hours_end:02d}:{minutes_end:02d}"
            itinerary_list.append({
                "action": "meet",
                "person": friend_data[i]['name'],
                "start_time": start_str,
                "end_time": end_str
            })
    itinerary_list.sort(key=lambda x: x['start_time'])
    result = {'itinerary': itinerary_list}
    print('SOLUTION:')
    print(json.dumps(result))
else:
    print('SOLUTION:')
    print(json.dumps({"itinerary": []}))