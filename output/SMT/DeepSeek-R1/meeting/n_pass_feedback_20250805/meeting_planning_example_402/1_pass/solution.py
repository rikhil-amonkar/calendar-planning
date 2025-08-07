from z3 import *
import json

def main():
    friends = {
        "Sarah": {"loc": "Haight-Ashbury", "start_avail": 480, "end_avail": 750, "min_dur": 105},
        "Patricia": {"loc": "Sunset District", "start_avail": 480, "end_avail": 645, "min_dur": 45},
        "Matthew": {"loc": "Marina District", "start_avail": 15, "end_avail": 180, "min_dur": 15},
        "Joseph": {"loc": "Financial District", "start_avail": 315, "end_avail": 585, "min_dur": 30},
        "Robert": {"loc": "Union Square", "start_avail": 75, "end_avail": 765, "min_dur": 15}
    }
    
    travel_times = {
        ("Golden Gate Park", "Haight-Ashbury"): 7,
        ("Golden Gate Park", "Sunset District"): 10,
        ("Golden Gate Park", "Marina District"): 16,
        ("Golden Gate Park", "Financial District"): 26,
        ("Golden Gate Park", "Union Square"): 22,
        ("Haight-Ashbury", "Golden Gate Park"): 7,
        ("Haight-Ashbury", "Sunset District"): 15,
        ("Haight-Ashbury", "Marina District"): 17,
        ("Haight-Ashbury", "Financial District"): 21,
        ("Haight-Ashbury", "Union Square"): 17,
        ("Sunset District", "Golden Gate Park"): 11,
        ("Sunset District", "Haight-Ashbury"): 15,
        ("Sunset District", "Marina District"): 21,
        ("Sunset District", "Financial District"): 30,
        ("Sunset District", "Union Square"): 30,
        ("Marina District", "Golden Gate Park"): 18,
        ("Marina District", "Haight-Ashbury"): 16,
        ("Marina District", "Sunset District"): 19,
        ("Marina District", "Financial District"): 17,
        ("Marina District", "Union Square"): 16,
        ("Financial District", "Golden Gate Park"): 23,
        ("Financial District", "Haight-Ashbury"): 19,
        ("Financial District", "Sunset District"): 31,
        ("Financial District", "Marina District"): 15,
        ("Financial District", "Union Square"): 9,
        ("Union Square", "Golden Gate Park"): 22,
        ("Union Square", "Haight-Ashbury"): 18,
        ("Union Square", "Sunset District"): 26,
        ("Union Square", "Marina District"): 18,
        ("Union Square", "Financial District"): 9
    }
    
    opt = Optimize()
    
    meet = {}
    order = {}
    start_time = {}
    for name in friends:
        meet[name] = Bool(name)
        order[name] = Int(f"order_{name}")
        start_time[name] = Int(f"start_{name}")
    
    dur = {name: friends[name]["min_dur"] for name in friends}
    
    for name in friends:
        opt.add(If(meet[name], And(order[name] >= 1, order[name] <= 5), order[name] == 0))
    
    friend_names = list(friends.keys())
    for i in range(len(friend_names)):
        for j in range(i+1, len(friend_names)):
            n1 = friend_names[i]
            n2 = friend_names[j]
            opt.add(If(And(meet[n1], meet[n2]), order[n1] != order[n2], True))
    
    for name in friends:
        s_avail = friends[name]["start_avail"]
        e_avail = friends[name]["end_avail"]
        d = dur[name]
        opt.add(If(meet[name],
                   And(start_time[name] >= s_avail, start_time[name] + d <= e_avail),
                   True))
    
    for name in friends:
        loc = friends[name]["loc"]
        travel_start = travel_times[("Golden Gate Park", loc)]
        opt.add(If(And(meet[name], order[name] == 1),
                   start_time[name] >= travel_start,
                   True))
    
    for name_i in friends:
        for name_j in friends:
            if name_i == name_j:
                continue
            loc_i = friends[name_i]["loc"]
            loc_j = friends[name_j]["loc"]
            travel_ij = travel_times[(loc_j, loc_i)]
            opt.add(If(And(meet[name_i], meet[name_j], order[name_i] == order[name_j] + 1),
                       start_time[name_i] >= start_time[name_j] + dur[name_j] + travel_ij,
                       True))
    
    total_meetings = Sum([If(meet[name], 1, 0) for name in friends])
    opt.maximize(total_meetings)
    
    itinerary = []
    if opt.check() == sat:
        m = opt.model()
        meetings = []
        for name in friends:
            if m.eval(meet[name]):
                start_val = m.eval(start_time[name])
                if isinstance(start_val, IntNumRef):
                    start_minutes = start_val.as_long()
                else:
                    start_minutes = start_val
                dur_val = dur[name]
                end_minutes = start_minutes + dur_val
                total_minutes_since_midnight_start = 9 * 60 + start_minutes
                hours = total_minutes_since_midnight_start // 60
                minutes = total_minutes_since_midnight_start % 60
                start_str = f"{hours:02d}:{minutes:02d}"
                total_minutes_since_midnight_end = 9 * 60 + end_minutes
                hours_end = total_minutes_since_midnight_end // 60
                minutes_end = total_minutes_since_midnight_end % 60
                end_str = f"{hours_end:02d}:{minutes_end:02d}"
                meetings.append({
                    'person': name,
                    'start_time': start_str,
                    'end_time': end_str,
                    'start_minutes': start_minutes
                })
        meetings.sort(key=lambda x: x['start_minutes'])
        itinerary = [{"action": "meet", "person": item['person'], "start_time": item['start_time'], "end_time": item['end_time']} for item in meetings]
    
    print("SOLUTION:")
    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()