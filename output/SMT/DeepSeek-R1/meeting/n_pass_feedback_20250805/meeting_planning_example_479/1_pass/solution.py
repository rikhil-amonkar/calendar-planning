from z3 import *
import json

def main():
    travel_matrix = [
        [0, 25, 21, 21, 20, 5],
        [25, 0, 7, 23, 11, 26],
        [20, 7, 0, 18, 15, 21],
        [19, 22, 19, 0, 31, 19],
        [20, 12, 15, 31, 0, 23],
        [4, 23, 19, 19, 22, 0]
    ]
    
    friends = [
        {"name": "Mary", "loc_index": 1, "window": (525, 705), "min_duration": 45},
        {"name": "Kevin", "loc_index": 2, "window": (615, 975), "min_duration": 90},
        {"name": "Deborah", "loc_index": 3, "window": (900, 1155), "min_duration": 120},
        {"name": "Stephanie", "loc_index": 4, "window": (600, 1035), "min_duration": 120},
        {"name": "Emily", "loc_index": 5, "window": (690, 1305), "min_duration": 105}
    ]
    n = len(friends)
    virtual_index = n
    virtual_time = 540
    virtual_loc = 0

    opt = Optimize()
    opt.set("timeout", 60000)

    meet = [Bool(f'meet_{i}') for i in range(n)]
    s = [Int(f's_{i}') for i in range(n)]
    
    before = [[None] * (n+1) for _ in range(n+1)]
    for i in range(n+1):
        for j in range(n+1):
            if i != j:
                before[i][j] = Bool(f'before_{i}_{j}')

    for i in range(n):
        opt.add(Implies(meet[i], before[virtual_index][i]))
        opt.add(Implies(meet[i], Not(before[i][virtual_index])))

    for i in range(n+1):
        for j in range(n+1):
            if i != j:
                opt.add(before[i][j] == Not(before[j][i]))

    for i in range(n):
        for j in range(i+1, n):
            opt.add(Implies(And(meet[i], meet[j]), Or(before[i][j], before[j][i])))

    for i in range(n+1):
        for j in range(n+1):
            for k in range(n+1):
                if i != j and i != k and j != k:
                    opt.add(Implies(And(before[i][j], before[j][k]), before[i][k]))

    for i in range(n):
        win_start, win_end = friends[i]['window']
        min_dur = friends[i]['min_duration']
        opt.add(Implies(meet[i], And(s[i] >= win_start, s[i] + min_dur <= win_end)))
        opt.add(Implies(meet[i], s[i] >= 0))

    for i in range(n+1):
        for j in range(n+1):
            if i == j:
                continue
            if i == virtual_index and j < n:
                tt = travel_matrix[virtual_loc][friends[j]['loc_index']]
                opt.add(Implies(And(meet[j], before[i][j]), s[j] >= virtual_time + tt))
            elif i < n and j < n:
                tt = travel_matrix[friends[i]['loc_index']][friends[j]['loc_index']]
                opt.add(Implies(And(meet[i], meet[j], before[i][j]), 
                               s[j] >= s[i] + friends[i]['min_duration'] + tt))

    total_meet = Sum([If(meet_i, 1, 0) for meet_i in meet])
    opt.maximize(total_meet)

    itinerary = []
    if opt.check() == sat:
        model = opt.model()
        meetings = []
        for i in range(n):
            if model.eval(meet[i]):
                start_val = model.eval(s[i])
                if isinstance(start_val, IntNumRef):
                    start_minutes = start_val.as_long()
                else:
                    start_minutes = int(str(start_val))
                min_dur = friends[i]['min_duration']
                end_minutes = start_minutes + min_dur
                start_str = f"{start_minutes // 60:02d}:{start_minutes % 60:02d}"
                end_str = f"{end_minutes // 60:02d}:{end_minutes % 60:02d}"
                meetings.append({
                    "action": "meet",
                    "person": friends[i]['name'],
                    "start_time": start_str,
                    "end_time": end_str
                })
        meetings.sort(key=lambda x: x['start_time'])
        itinerary = meetings
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()