from z3 import *
import json

def main():
    friends = [
        {"name": "Betty", "location": "Russian Hill", "start_avail": 0, "end_avail": 870, "duration": 105},
        {"name": "Melissa", "location": "Alamo Square", "start_avail": 30, "end_avail": 495, "duration": 105},
        {"name": "Joshua", "location": "Haight-Ashbury", "start_avail": 195, "end_avail": 780, "duration": 90},
        {"name": "Jeffrey", "location": "Marina District", "start_avail": 195, "end_avail": 720, "duration": 45},
        {"name": "James", "location": "Bayview", "start_avail": 0, "end_avail": 660, "duration": 90},
        {"name": "Anthony", "location": "Chinatown", "start_avail": 165, "end_avail": 270, "duration": 75},
        {"name": "Timothy", "location": "Presidio", "start_avail": 210, "end_avail": 345, "duration": 90},
        {"name": "Emily", "location": "Sunset District", "start_avail": 630, "end_avail": 750, "duration": 120}
    ]
    
    travel_times = {
        ("Union Square", "Russian Hill"): 13,
        ("Union Square", "Alamo Square"): 15,
        ("Union Square", "Haight-Ashbury"): 18,
        ("Union Square", "Marina District"): 18,
        ("Union Square", "Bayview"): 15,
        ("Union Square", "Chinatown"): 7,
        ("Union Square", "Presidio"): 24,
        ("Union Square", "Sunset District"): 27,
        ("Russian Hill", "Union Square"): 10,
        ("Russian Hill", "Alamo Square"): 15,
        ("Russian Hill", "Haight-Ashbury"): 17,
        ("Russian Hill", "Marina District"): 7,
        ("Russian Hill", "Bayview"): 23,
        ("Russian Hill", "Chinatown"): 9,
        ("Russian Hill", "Presidio"): 14,
        ("Russian Hill", "Sunset District"): 23,
        ("Alamo Square", "Union Square"): 14,
        ("Alamo Square", "Russian Hill"): 13,
        ("Alamo Square", "Haight-Ashbury"): 5,
        ("Alamo Square", "Marina District"): 15,
        ("Alamo Square", "Bayview"): 16,
        ("Alamo Square", "Chinatown"): 15,
        ("Alamo Square", "Presidio"): 17,
        ("Alamo Square", "Sunset District"): 16,
        ("Haight-Ashbury", "Union Square"): 19,
        ("Haight-Ashbury", "Russian Hill"): 17,
        ("Haight-Ashbury", "Alamo Square"): 5,
        ("Haight-Ashbury", "Marina District"): 17,
        ("Haight-Ashbury", "Bayview"): 18,
        ("Haight-Ashbury", "Chinatown"): 19,
        ("Haight-Ashbury", "Presidio"): 15,
        ("Haight-Ashbury", "Sunset District"): 15,
        ("Marina District", "Union Square"): 16,
        ("Marina District", "Russian Hill"): 8,
        ("Marina District", "Alamo Square"): 15,
        ("Marina District", "Haight-Ashbury"): 16,
        ("Marina District", "Bayview"): 27,
        ("Marina District", "Chinatown"): 15,
        ("Marina District", "Presidio"): 10,
        ("Marina District", "Sunset District"): 19,
        ("Bayview", "Union Square"): 18,
        ("Bayview", "Russian Hill"): 23,
        ("Bayview", "Alamo Square"): 16,
        ("Bayview", "Haight-Ashbury"): 19,
        ("Bayview", "Marina District"): 27,
        ("Bayview", "Chinatown"): 19,
        ("Bayview", "Presidio"): 32,
        ("Bayview", "Sunset District"): 23,
        ("Chinatown", "Union Square"): 7,
        ("Chinatown", "Russian Hill"): 7,
        ("Chinatown", "Alamo Square"): 17,
        ("Chinatown", "Haight-Ashbury"): 19,
        ("Chinatown", "Marina District"): 12,
        ("Chinatown", "Bayview"): 20,
        ("Chinatown", "Presidio"): 19,
        ("Chinatown", "Sunset District"): 29,
        ("Presidio", "Union Square"): 22,
        ("Presidio", "Russian Hill"): 14,
        ("Presidio", "Alamo Square"): 19,
        ("Presidio", "Haight-Ashbury"): 15,
        ("Presidio", "Marina District"): 11,
        ("Presidio", "Bayview"): 31,
        ("Presidio", "Chinatown"): 21,
        ("Presidio", "Sunset District"): 15,
        ("Sunset District", "Union Square"): 30,
        ("Sunset District", "Russian Hill"): 24,
        ("Sunset District", "Alamo Square"): 17,
        ("Sunset District", "Haight-Ashbury"): 15,
        ("Sunset District", "Marina District"): 21,
        ("Sunset District", "Bayview"): 22,
        ("Sunset District", "Chinatown"): 30,
        ("Sunset District", "Presidio"): 16
    }

    opt = Optimize()
    n = len(friends)
    
    meet_vars = [Bool(f"meet_{f['name']}") for f in friends]
    start_vars = [Int(f"start_{f['name']}") for f in friends]
    
    for i, friend in enumerate(friends):
        opt.add(Implies(meet_vars[i], start_vars[i] >= friend['start_avail']))
        opt.add(Implies(meet_vars[i], start_vars[i] + friend['duration'] <= friend['end_avail']))
    
    before = [[Bool(f"before_{i}_{j}") if i != j else None for j in range(n)] for i in range(n)]
    for i in range(n):
        for j in range(n):
            if i != j:
                opt.add(Implies(And(meet_vars[i], meet_vars[j]), Or(before[i][j], before[j][i])))
                opt.add(Implies(And(meet_vars[i], meet_vars[j]), Not(And(before[i][j], before[j][i]))))
                
    for i in range(n):
        for j in range(n):
            if i != j:
                for k in range(n):
                    if k != i and k != j:
                        opt.add(Implies(And(before[i][j], before[j][k]), before[i][k]))
    
    for i in range(n):
        for j in range(n):
            if i != j:
                loc_i = friends[i]['location']
                loc_j = friends[j]['location']
                travel_time_ij = travel_times[(loc_i, loc_j)]
                opt.add(Implies(And(meet_vars[i], meet_vars[j], before[i][j]),
                                  start_vars[j] >= start_vars[i] + friends[i]['duration'] + travel_time_ij))
    
    for i in range(n):
        no_prior = And([ Or(Not(meet_vars[j]), Not(before[j][i])) for j in range(n) if j != i ])
        travel_time_to_i = travel_times[("Union Square", friends[i]['location'])]
        opt.add(Implies(And(meet_vars[i], no_prior), start_vars[i] >= travel_time_to_i))
        
    for i in range(n):
        no_after = And([ Or(Not(meet_vars[j]), Not(before[i][j])) for j in range(n) if j != i ])
        travel_time_back = travel_times.get((friends[i]['location'], "Union Square"))
        opt.add(Implies(And(meet_vars[i], no_after), 
                             start_vars[i] + friends[i]['duration'] + travel_time_back <= 870))
    
    total_meetings = Sum([If(meet_vars[i], 1, 0) for i in range(n)])
    opt.maximize(total_meetings)
    
    if opt.check() == sat:
        model = opt.model()
        scheduled_meetings = []
        for i, friend in enumerate(friends):
            if model.eval(meet_vars[i]):
                start_val = model.eval(start_vars[i])
                start_minutes = start_val.as_long() if isinstance(start_val, IntNumRef) else int(str(start_val))
                scheduled_meetings.append({
                    'name': friend['name'],
                    'start_minutes': start_minutes,
                    'duration': friend['duration']
                })
        
        scheduled_meetings.sort(key=lambda x: x['start_minutes'])
        itinerary = []
        for meet in scheduled_meetings:
            total_minutes_start = meet['start_minutes']
            hours_start = total_minutes_start // 60
            minutes_start = total_minutes_start % 60
            start_hour = 9 + hours_start
            start_time_str = f"{start_hour:02d}:{minutes_start:02d}"
            
            end_minutes = total_minutes_start + meet['duration']
            hours_end = end_minutes // 60
            minutes_end = end_minutes % 60
            end_hour = 9 + hours_end
            end_time_str = f"{end_hour:02d}:{minutes_end:02d}"
            
            itinerary.append({
                "action": "meet",
                "person": meet['name'],
                "start_time": start_time_str,
                "end_time": end_time_str
            })
        
        result = {"itinerary": itinerary}
        print("SOLUTION:")
        print(json.dumps(result))
    else:
        print("SOLUTION:")
        print(json.dumps({"itinerary": []}))

if __name__ == '__main__':
    main()