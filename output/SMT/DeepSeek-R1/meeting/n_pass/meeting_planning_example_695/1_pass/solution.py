import json
from z3 import *

def format_time(minutes_from_9am):
    total_minutes = minutes_from_9am
    h = total_minutes // 60
    m = total_minutes % 60
    abs_hour = 9 + h
    return f"{abs_hour:02d}:{m:02d}"

def main():
    names = ["Dummy", "Paul", "Carol", "Patricia", "Karen", "Nancy", "Jeffrey", "Matthew"]
    locations = [
        "Bayview",          # Dummy
        "Nob Hill",         # Paul
        "Union Square",     # Carol
        "Chinatown",        # Patricia
        "The Castro",       # Karen
        "Presidio",         # Nancy
        "Pacific Heights",  # Jeffrey
        "Russian Hill"      # Matthew
    ]
    min_times = [0, 60, 120, 75, 45, 30, 45, 75]
    avail = [
        (0, 0),             # Dummy
        (435, 735),         # Paul: 4:15 PM to 9:15 PM
        (540, 675),         # Carol: 6:00 PM to 8:15 PM
        (660, 750),         # Patricia: 8:00 PM to 9:30 PM
        (480, 600),         # Karen: 5:00 PM to 7:00 PM
        (165, 780),         # Nancy: 11:45 AM to 10:00 PM
        (660, 705),         # Jeffrey: 8:00 PM to 8:45 PM
        (405, 765)          # Matthew: 3:45 PM to 9:45 PM
    ]
    
    travel_dict = {
        "Bayview": {
            "Nob Hill": 20,
            "Union Square": 17,
            "Chinatown": 18,
            "The Castro": 20,
            "Presidio": 31,
            "Pacific Heights": 23,
            "Russian Hill": 23
        },
        "Nob Hill": {
            "Bayview": 19,
            "Union Square": 7,
            "Chinatown": 6,
            "The Castro": 17,
            "Presidio": 17,
            "Pacific Heights": 8,
            "Russian Hill": 5
        },
        "Union Square": {
            "Bayview": 15,
            "Nob Hill": 9,
            "Chinatown": 7,
            "The Castro": 19,
            "Presidio": 24,
            "Pacific Heights": 15,
            "Russian Hill": 13
        },
        "Chinatown": {
            "Bayview": 22,
            "Nob Hill": 8,
            "Union Square": 7,
            "The Castro": 22,
            "Presidio": 19,
            "Pacific Heights": 10,
            "Russian Hill": 7
        },
        "The Castro": {
            "Bayview": 19,
            "Nob Hill": 16,
            "Union Square": 19,
            "Chinatown": 20,
            "Presidio": 20,
            "Pacific Heights": 16,
            "Russian Hill": 18
        },
        "Presidio": {
            "Bayview": 31,
            "Nob Hill": 18,
            "Union Square": 22,
            "Chinatown": 21,
            "The Castro": 21,
            "Pacific Heights": 11,
            "Russian Hill": 14
        },
        "Pacific Heights": {
            "Bayview": 22,
            "Nob Hill": 8,
            "Union Square": 12,
            "Chinatown": 11,
            "The Castro": 16,
            "Presidio": 11,
            "Russian Hill": 7
        },
        "Russian Hill": {
            "Bayview": 23,
            "Nob Hill": 5,
            "Union Square": 11,
            "Chinatown": 9,
            "The Castro": 21,
            "Presidio": 14,
            "Pacific Heights": 7
        }
    }
    
    n = len(names)
    opt = Optimize()
    
    B = [Bool(f'B_{i}') for i in range(n)]
    S = [Int(f'S_{i}') for i in range(n)]
    E = [Int(f'E_{i}') for i in range(n)]
    P = [Int(f'P_{i}') for i in range(n)]
    
    # Fix dummy meeting
    opt.add(B[0] == True)
    opt.add(S[0] == 0)
    opt.add(E[0] == 0)
    opt.add(P[0] == 0)
    
    # Constraints for meetings 1 to 7
    for i in range(1, n):
        opt.add(Implies(B[i], 
                        And(S[i] >= avail[i][0],
                            E[i] == S[i] + min_times[i],
                            E[i] <= avail[i][1],
                            P[i] >= 1,
                            P[i] <= 7
                        )))
        opt.add(Implies(Not(B[i]), P[i] == -1))
    
    # Distinct positions for attended meetings
    for i in range(n):
        for j in range(i+1, n):
            opt.add(Implies(And(B[i], B[j]), P[i] != P[j]))
    
    # Travel constraints
    for i in range(n):
        for j in range(n):
            if i == j:
                continue
            loc_i = locations[i]
            loc_j = locations[j]
            travel_time = travel_dict[loc_i][loc_j]
            opt.add(Implies(And(B[i], B[j], P[i] < P[j]),
                           E[i] + travel_time <= S[j]))
    
    # Objective: maximize number of meetings
    num_meetings = Sum([If(B[i], 1, 0) for i in range(1, n)])
    opt.maximize(num_meetings)
    
    if opt.check() == sat:
        m = opt.model()
        meeting_list = []
        for i in range(1, n):
            if m.evaluate(B[i]):
                start_val = m.evaluate(S[i])
                if not isinstance(start_val, IntNumRef):
                    continue
                start_min = start_val.as_long()
                end_min = start_min + min_times[i]
                pos_val = m.evaluate(P[i]).as_long()
                start_str = format_time(start_min)
                end_str = format_time(end_min)
                meeting_list.append((pos_val, {
                    "action": "meet",
                    "person": names[i],
                    "start_time": start_str,
                    "end_time": end_str
                }))
        meeting_list.sort(key=lambda x: x[0])
        itinerary = [item[1] for item in meeting_list]
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == '__main__':
    main()