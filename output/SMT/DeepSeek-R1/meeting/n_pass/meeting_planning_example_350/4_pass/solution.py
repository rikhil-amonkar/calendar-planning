from z3 import *
import json

def main():
    friends = [
        ('Mary', 'Pacific Heights', 60, 600, 45),
        ('Lisa', 'Mission District', 690, 780, 75),
        ('Betty', 'Haight-Ashbury', 0, 495, 90),
        ('Charles', 'Financial District', 135, 360, 120)
    ]
    
    travel_times = {
        "Bayview": {
            "Pacific Heights": 23, "Mission District": 13,
            "Haight-Ashbury": 19, "Financial District": 19
        },
        "Pacific Heights": {
            "Bayview": 22, "Mission District": 15,
            "Haight-Ashbury": 11, "Financial District": 13
        },
        "Mission District": {
            "Bayview": 15, "Pacific Heights": 16,
            "Haight-Ashbury": 12, "Financial District": 17
        },
        "Haight-Ashbury": {
            "Bayview": 18, "Pacific Heights": 12,
            "Mission District": 11, "Financial District": 21
        },
        "Financial District": {
            "Bayview": 19, "Pacific Heights": 13,
            "Mission District": 17, "Haight-Ashbury": 19
        }
    }
    
    s = Optimize()
    
    meet_vars = [Bool(f"meet_{name}") for (name, *_) in friends]
    start_vars = [Int(f"start_{name}") for (name, *_) in friends]
    pos_vars = [Int(f"pos_{name}") for (name, *_) in friends]
    
    total_meetings = Sum([If(v, 1, 0) for v in meet_vars])
    
    for idx, (name, loc, avail_start, avail_end, dur) in enumerate(friends):
        s.add(Implies(meet_vars[idx], 
                      And(start_vars[idx] >= avail_start,
                          start_vars[idx] + dur <= avail_end,
                          pos_vars[idx] >= 0,
                          pos_vars[idx] < 4)))
        s.add(Implies(Not(meet_vars[idx]), pos_vars[idx] == -(idx+1)))
    
    s.add(Distinct(pos_vars))
    
    n = total_meetings
    for i in range(4):
        cond_list = [And(meet_vars[j], pos_vars[j] == i) for j in range(4)]
        s.add(Implies(i < n, Or(cond_list)))
    
    for idx, (name, loc, *_) in enumerate(friends):
        s.add(Implies(And(meet_vars[idx], pos_vars[idx] == 0),
                      start_vars[idx] >= travel_times['Bayview'][loc]))
    
    for i in range(4):
        for j in range(4):
            if i == j:
                continue
            name_i, loc_i, avail_start_i, avail_end_i, dur_i = friends[i]
            name_j, loc_j, avail_start_j, avail_end_j, dur_j = friends[j]
            cond = And(meet_vars[i], meet_vars[j], pos_vars[j] == pos_vars[i] + 1)
            s.add(Implies(cond, 
                         start_vars[i] + dur_i + travel_times[loc_i][loc_j] <= start_vars[j]))
    
    s.maximize(total_meetings)
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for idx, (name, loc, avail_start, avail_end, dur) in enumerate(friends):
            if m.evaluate(meet_vars[idx]):
                start_val = m.evaluate(start_vars[idx])
                start_minutes = start_val.as_long()
                end_minutes = start_minutes + dur
                hour_start = 9 + start_minutes // 60
                minute_start = start_minutes % 60
                hour_end = 9 + end_minutes // 60
                minute_end = end_minutes % 60
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": f"{hour_start:02d}:{minute_start:02d}",
                    "end_time": f"{hour_end:02d}:{minute_end:02d}"
                })
        itinerary.sort(key=lambda x: x['start_time'])
        print("SOLUTION:")
        print(json.dumps({"itinerary": itinerary}))
    else:
        print("SOLUTION:")
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()