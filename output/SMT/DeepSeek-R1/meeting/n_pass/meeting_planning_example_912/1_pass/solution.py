from z3 import *
import json

def main():
    friends = [
        ("Kimberly", "Presidio", 930, 960, 15),
        ("Elizabeth", "Alamo Square", 1155, 1215, 15),
        ("Joshua", "Marina District", 630, 855, 45),
        ("Sandra", "Financial District", 1170, 1215, 45),
        ("Kenneth", "Nob Hill", 765, 1305, 30),
        ("Betty", "Sunset District", 840, 1140, 60),
        ("Deborah", "Chinatown", 1035, 1230, 15),
        ("Barbara", "Russian Hill", 1050, 1275, 120),
        ("Steven", "North Beach", 1065, 1245, 90),
        ("Daniel", "Haight-Ashbury", 1110, 1125, 15)
    ]
    
    locations = [
        "Union Square",   #0
        "Presidio",        #1
        "Alamo Square",    #2
        "Marina District", #3
        "Financial District", #4
        "Nob Hill",        #5
        "Sunset District", #6
        "Chinatown",       #7
        "Russian Hill",    #8
        "North Beach",     #9
        "Haight-Ashbury"   #10
    ]
    
    travel_time_dict = {
        ("Union Square", "Presidio"): 24,
        ("Union Square", "Alamo Square"): 15,
        ("Union Square", "Marina District"): 18,
        ("Union Square", "Financial District"): 9,
        ("Union Square", "Nob Hill"): 9,
        ("Union Square", "Sunset District"): 27,
        ("Union Square", "Chinatown"): 7,
        ("Union Square", "Russian Hill"): 13,
        ("Union Square", "North Beach"): 10,
        ("Union Square", "Haight-Ashbury"): 18,
        ("Presidio", "Union Square"): 22,
        ("Presidio", "Alamo Square"): 19,
        ("Presidio", "Marina District"): 11,
        ("Presidio", "Financial District"): 23,
        ("Presidio", "Nob Hill"): 18,
        ("Presidio", "Sunset District"): 15,
        ("Presidio", "Chinatown"): 21,
        ("Presidio", "Russian Hill"): 14,
        ("Presidio", "North Beach"): 18,
        ("Presidio", "Haight-Ashbury"): 15,
        ("Alamo Square", "Union Square"): 14,
        ("Alamo Square", "Presidio"): 17,
        ("Alamo Square", "Marina District"): 15,
        ("Alamo Square", "Financial District"): 17,
        ("Alamo Square", "Nob Hill"): 11,
        ("Alamo Square", "Sunset District"): 16,
        ("Alamo Square", "Chinatown"): 15,
        ("Alamo Square", "Russian Hill"): 13,
        ("Alamo Square", "North Beach"): 15,
        ("Alamo Square", "Haight-Ashbury"): 5,
        ("Marina District", "Union Square"): 16,
        ("Marina District", "Presidio"): 10,
        ("Marina District", "Alamo Square"): 15,
        ("Marina District", "Financial District"): 17,
        ("Marina District", "Nob Hill"): 12,
        ("Marina District", "Sunset District"): 19,
        ("Marina District", "Chinatown"): 15,
        ("Marina District", "Russian Hill"): 8,
        ("Marina District", "North Beach"): 11,
        ("Marina District", "Haight-Ashbury"): 16,
        ("Financial District", "Union Square"): 9,
        ("Financial District", "Presidio"): 22,
        ("Financial District", "Alamo Square"): 17,
        ("Financial District", "Marina District"): 15,
        ("Financial District", "Nob Hill"): 8,
        ("Financial District", "Sunset District"): 30,
        ("Financial District", "Chinatown"): 5,
        ("Financial District", "Russian Hill"): 11,
        ("Financial District", "North Beach"): 7,
        ("Financial District", "Haight-Ashbury"): 19,
        ("Nob Hill", "Union Square"): 7,
        ("Nob Hill", "Presidio"): 17,
        ("Nob Hill", "Alamo Square"): 11,
        ("Nob Hill", "Marina District"): 11,
        ("Nob Hill", "Financial District"): 9,
        ("Nob Hill", "Sunset District"): 24,
        ("Nob Hill", "Chinatown"): 6,
        ("Nob Hill", "Russian Hill"): 5,
        ("Nob Hill", "North Beach"): 8,
        ("Nob Hill", "Haight-Ashbury"): 13,
        ("Sunset District", "Union Square"): 30,
        ("Sunset District", "Presidio"): 16,
        ("Sunset District", "Alamo Square"): 17,
        ("Sunset District", "Marina District"): 21,
        ("Sunset District", "Financial District"): 30,
        ("Sunset District", "Nob Hill"): 27,
        ("Sunset District", "Chinatown"): 30,
        ("Sunset District", "Russian Hill"): 24,
        ("Sunset District", "North Beach"): 28,
        ("Sunset District", "Haight-Ashbury"): 15,
        ("Chinatown", "Union Square"): 7,
        ("Chinatown", "Presidio"): 19,
        ("Chinatown", "Alamo Square"): 17,
        ("Chinatown", "Marina District"): 12,
        ("Chinatown", "Financial District"): 5,
        ("Chinatown", "Nob Hill"): 9,
        ("Chinatown", "Sunset District"): 29,
        ("Chinatown", "Russian Hill"): 7,
        ("Chinatown", "North Beach"): 3,
        ("Chinatown", "Haight-Ashbury"): 19,
        ("Russian Hill", "Union Square"): 10,
        ("Russian Hill", "Presidio"): 14,
        ("Russian Hill", "Alamo Square"): 15,
        ("Russian Hill", "Marina District"): 7,
        ("Russian Hill", "Financial District"): 11,
        ("Russian Hill", "Nob Hill"): 5,
        ("Russian Hill", "Sunset District"): 23,
        ("Russian Hill", "Chinatown"): 9,
        ("Russian Hill", "North Beach"): 5,
        ("Russian Hill", "Haight-Ashbury"): 17,
        ("North Beach", "Union Square"): 7,
        ("North Beach", "Presidio"): 17,
        ("North Beach", "Alamo Square"): 16,
        ("North Beach", "Marina District"): 9,
        ("North Beach", "Financial District"): 8,
        ("North Beach", "Nob Hill"): 7,
        ("North Beach", "Sunset District"): 27,
        ("North Beach", "Chinatown"): 6,
        ("North Beach", "Russian Hill"): 4,
        ("North Beach", "Haight-Ashbury"): 18,
        ("Haight-Ashbury", "Union Square"): 19,
        ("Haight-Ashbury", "Presidio"): 15,
        ("Haight-Ashbury", "Alamo Square"): 5,
        ("Haight-Ashbury", "Marina District"): 17,
        ("Haight-Ashbury", "Financial District"): 21,
        ("Haight-Ashbury", "Nob Hill"): 15,
        ("Haight-Ashbury", "Sunset District"): 15,
        ("Haight-Ashbury", "Chinatown"): 19,
        ("Haight-Ashbury", "Russian Hill"): 17,
        ("Haight-Ashbury", "North Beach"): 19
    }
    
    loc_to_index = {loc: idx for idx, loc in enumerate(locations)}
    
    travel_time = [[0]*11 for _ in range(11)]
    for i in range(11):
        for j in range(11):
            if i == j:
                travel_time[i][j] = 0
            else:
                from_loc = locations[i]
                to_loc = locations[j]
                key = (from_loc, to_loc)
                travel_time[i][j] = travel_time_dict[key]
    
    s = Optimize()
    
    meet = [Bool(f"meet_{i}") for i in range(10)]
    start = [Real(f"start_{i}") for i in range(10)]
    end = [Real(f"end_{i}") for i in range(10)]
    
    u = [Int(f"u_{i}") for i in range(11)]
    z = [[Bool(f"z_{i}_{j}") for j in range(10)] for i in range(11)]
    
    meet_count = Int("meet_count")
    s.add(meet_count == Sum([If(meet_i, 1, 0) for meet_i in meet]))
    
    s.add(u[0] == 0)
    
    for i in range(10):
        _, _, win_start, win_end, min_dur = friends[i]
        s.add(If(meet[i],
                 And(start[i] >= win_start,
                     end[i] == start[i] + min_dur,
                     end[i] <= win_end,
                     u[i+1] >= 1,
                     u[i+1] <= meet_count),
                 True))
    
    s.add(If(meet_count >= 1, 
             Sum([z[0][j] for j in range(10)]) == 1, 
             Sum([z[0][j] for j in range(10)]) == 0))
    
    for j in range(10):
        in_degree = Sum([z[i][j] for i in range(11)])
        s.add(in_degree == If(meet[j], 1, 0))
    
    for i in range(1, 11):
        fi = i - 1
        out_degree = Sum([z[i][j] for j in range(10)])
        s.add(If(meet[fi], out_degree <= 1, out_degree == 0))
    
    total_edges = Sum([z[i][j] for i in range(11) for j in range(10)])
    s.add(total_edges == meet_count)
    
    for i in range(11):
        for j in range(10):
            s.add(If(z[i][j], u[j+1] >= u[i] + 1, True))
    
    for i in range(11):
        for j in range(10):
            if i == 0:
                s.add(If(z[i][j], start[j] >= 540 + travel_time[0][j+1], True))
            else:
                fi = i - 1
                s.add(If(z[i][j], start[j] >= end[fi] + travel_time[i][j+1], True))
    
    s.maximize(meet_count)
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(10):
            if is_true(m[meet[i]]):
                name = friends[i][0]
                start_val = m[start[i]]
                end_val = m[end[i]]
                if is_int_value(start_val):
                    start_min = start_val.as_long()
                else:
                    start_min = int(str(start_val))
                if is_int_value(end_val):
                    end_min = end_val.as_long()
                else:
                    end_min = int(str(end_val))
                start_h = start_min // 60
                start_m = start_min % 60
                end_h = end_min // 60
                end_m = end_min % 60
                start_time = f"{start_h:02d}:{start_m:02d}"
                end_time = f"{end_h:02d}:{end_m:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": start_time,
                    "end_time": end_time
                })
        itinerary.sort(key=lambda x: x['start_time'])
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()