import json
from z3 import *

def main():
    friends = [
        {"name": "Start", "district": "Sunset District", "start_avail": 0, "end_avail": 0, "min_dur": 0},
        {"name": "Karen", "district": "Russian Hill", "start_avail": 705, "end_avail": 765, "min_dur": 60},
        {"name": "Jessica", "district": "The Castro", "start_avail": 405, "end_avail": 630, "min_dur": 60},
        {"name": "Matthew", "district": "Richmond District", "start_avail": 0, "end_avail": 375, "min_dur": 15},
        {"name": "Michelle", "district": "Marina District", "start_avail": 90, "end_avail": 585, "min_dur": 75},
        {"name": "Carol", "district": "North Beach", "start_avail": 180, "end_avail": 480, "min_dur": 90},
        {"name": "Stephanie", "district": "Union Square", "start_avail": 105, "end_avail": 315, "min_dur": 30},
        {"name": "Linda", "district": "Golden Gate Park", "start_avail": 105, "end_avail": 780, "min_dur": 90}
    ]
    
    travel_times = [
        ("Sunset District", "Russian Hill", 24),
        ("Sunset District", "The Castro", 17),
        ("Sunset District", "Richmond District", 12),
        ("Sunset District", "Marina District", 21),
        ("Sunset District", "North Beach", 29),
        ("Sunset District", "Union Square", 30),
        ("Sunset District", "Golden Gate Park", 11),
        ("Russian Hill", "Sunset District", 23),
        ("Russian Hill", "The Castro", 21),
        ("Russian Hill", "Richmond District", 14),
        ("Russian Hill", "Marina District", 7),
        ("Russian Hill", "North Beach", 5),
        ("Russian Hill", "Union Square", 11),
        ("Russian Hill", "Golden Gate Park", 21),
        ("The Castro", "Sunset District", 17),
        ("The Castro", "Russian Hill", 18),
        ("The Castro", "Richmond District", 16),
        ("The Castro", "Marina District", 21),
        ("The Castro", "North Beach", 20),
        ("The Castro", "Union Square", 19),
        ("The Castro", "Golden Gate Park", 11),
        ("Richmond District", "Sunset District", 11),
        ("Richmond District", "Russian Hill", 13),
        ("Richmond District", "The Castro", 16),
        ("Richmond District", "Marina District", 9),
        ("Richmond District", "North Beach", 17),
        ("Richmond District", "Union Square", 21),
        ("Richmond District", "Golden Gate Park", 9),
        ("Marina District", "Sunset District", 19),
        ("Marina District", "Russian Hill", 8),
        ("Marina District", "The Castro", 22),
        ("Marina District", "Richmond District", 11),
        ("Marina District", "North Beach", 11),
        ("Marina District", "Union Square", 16),
        ("Marina District", "Golden Gate Park", 18),
        ("North Beach", "Sunset District", 27),
        ("North Beach", "Russian Hill", 4),
        ("North Beach", "The Castro", 22),
        ("North Beach", "Richmond District", 18),
        ("North Beach", "Marina District", 9),
        ("North Beach", "Union Square", 7),
        ("North Beach", "Golden Gate Park", 22),
        ("Union Square", "Sunset District", 26),
        ("Union Square", "Russian Hill", 13),
        ("Union Square", "The Castro", 19),
        ("Union Square", "Richmond District", 20),
        ("Union Square", "Marina District", 18),
        ("Union Square", "North Beach", 10),
        ("Union Square", "Golden Gate Park", 22),
        ("Golden Gate Park", "Sunset District", 10),
        ("Golden Gate Park", "Russian Hill", 19),
        ("Golden Gate Park", "The Castro", 13),
        ("Golden Gate Park", "Richmond District", 7),
        ("Golden Gate Park", "Marina District", 16),
        ("Golden Gate Park", "North Beach", 24),
        ("Golden Gate Park", "Union Square", 22)
    ]
    
    travel_dict = {}
    for (frm, to, t) in travel_times:
        travel_dict[(frm, to)] = t
        
    districts = [f["district"] for f in friends]
    n = len(friends)
    travel_matrix = [[0] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            if i == j:
                travel_matrix[i][j] = 0
            else:
                travel_matrix[i][j] = travel_dict[(districts[i], districts[j])]
    
    s = [Int(f's_{i}') for i in range(n)]
    meet = [Bool(f'meet_{i}') for i in range(n)]
    
    solver = Solver()
    solver.add(meet[0] == True)
    solver.add(s[0] == 0)
    
    for i in range(1, n):
        solver.add(Implies(meet[i], s[i] >= travel_matrix[0][i]))
        solver.add(Implies(meet[i], s[i] >= friends[i]["start_avail"]))
        solver.add(Implies(meet[i], s[i] + friends[i]["min_dur"] <= friends[i]["end_avail"]))
    
    for i in range(1, n):
        for j in range(1, n):
            if i != j:
                solver.add(Implies(And(meet[i], meet[j]),
                            Or(s[i] + friends[i]["min_dur"] + travel_matrix[i][j] <= s[j],
                               s[j] + friends[j]["min_dur"] + travel_matrix[j][i] <= s[i])))
    
    opt = Optimize()
    for c in solver.assertions():
        opt.add(c)
    
    meet_count = Sum([If(meet[i], 1, 0) for i in range(1, n)])
    opt.maximize(meet_count)
    
    if opt.check() == sat:
        m = opt.model()
        result_meetings = []
        for i in range(1, n):
            if is_true(m.eval(meet[i])):
                start_val = m.eval(s[i])
                start_min = start_val.as_long()
                dur = friends[i]["min_dur"]
                total_min = start_min
                hour = 9 + total_min // 60
                minute = total_min % 60
                start_time = f"{hour:02d}:{minute:02d}"
                end_min = start_min + dur
                hour_end = 9 + end_min // 60
                minute_end = end_min % 60
                end_time = f"{hour_end:02d}:{minute_end:02d}"
                result_meetings.append({
                    "action": "meet",
                    "person": friends[i]["name"],
                    "start_time": start_time,
                    "end_time": end_time
                })
        result_meetings.sort(key=lambda x: (int(x['start_time'].split(':')[0])*60 + int(x['start_time'].split(':')[1])))
        print('SOLUTION:')
        print(json.dumps({"itinerary": result_meetings}))
    else:
        print('SOLUTION:')
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()