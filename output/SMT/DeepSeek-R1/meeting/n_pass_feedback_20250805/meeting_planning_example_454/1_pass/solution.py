from z3 import *
import json

def main():
    travel_dict = {
        ("Presidio", "Mission District"): 26,
        ("Presidio", "Chinatown"): 21,
        ("Presidio", "Golden Gate Park"): 12,
        ("Presidio", "North Beach"): 18,
        ("Presidio", "Bayview"): 31,
        ("Mission District", "Presidio"): 25,
        ("Mission District", "Chinatown"): 16,
        ("Mission District", "Golden Gate Park"): 17,
        ("Mission District", "North Beach"): 17,
        ("Mission District", "Bayview"): 15,
        ("Chinatown", "Presidio"): 19,
        ("Chinatown", "Mission District"): 18,
        ("Chinatown", "Golden Gate Park"): 23,
        ("Chinatown", "North Beach"): 3,
        ("Chinatown", "Bayview"): 22,
        ("Golden Gate Park", "Presidio"): 11,
        ("Golden Gate Park", "Mission District"): 17,
        ("Golden Gate Park", "Chinatown"): 23,
        ("Golden Gate Park", "North Beach"): 24,
        ("Golden Gate Park", "Bayview"): 23,
        ("North Beach", "Presidio"): 17,
        ("North Beach", "Mission District"): 17,
        ("North Beach", "Chinatown"): 6,
        ("North Beach", "Golden Gate Park"): 22,
        ("North Beach", "Bayview"): 22,
        ("Bayview", "Presidio"): 31,
        ("Bayview", "Mission District"): 13,
        ("Bayview", "Chinatown"): 18,
        ("Bayview", "Golden Gate Park"): 22,
        ("Bayview", "North Beach"): 21
    }
    
    friend_names = ["Daniel", "Ronald", "Jessica", "William", "Ashley"]
    locations = {
        "Daniel": "Mission District",
        "Ronald": "Chinatown",
        "Jessica": "Golden Gate Park",
        "William": "North Beach",
        "Ashley": "Bayview"
    }
    avail = [
        (7*60, 11*60+15),    # Daniel: 7:00 to 11:15
        (7*60+15, 14*60+45), # Ronald: 7:15 to 14:45 (2:45 PM)
        (13*60+45, 15*60),   # Jessica: 1:45 PM to 3:00 PM
        (13*60+15, 20*60+15), # William: 1:15 PM to 8:15 PM
        (17*60+15, 20*60)    # Ashley: 5:15 PM to 8:00 PM
    ]
    durations = [105, 90, 30, 15, 105]
    
    s = [Int(f's_{i}') for i in range(5)]
    e = [Int(f'e_{i}') for i in range(5)]
    
    order = [Int(f'order_{i}') for i in range(5)]
    
    s_start = 9 * 60  # 9:00 AM in minutes
    
    solver = Solver()
    
    for i in range(5):
        solver.add(order[i] >= 0, order[i] < 5)
    solver.add(Distinct(order))
    
    for i in range(5):
        solver.add(s[i] >= avail[i][0])
        solver.add(e[i] <= avail[i][1])
        solver.add(e[i] == s[i] + durations[i])
    
    first_friend = order[0]
    for i in range(5):
        loc_i = locations[friend_names[i]]
        travel_time_start = travel_dict[("Presidio", loc_i)]
        solver.add(Implies(first_friend == i, s[i] >= s_start + travel_time_start))
    
    for idx in range(4):
        i_var = order[idx]
        j_var = order[idx+1]
        for i in range(5):
            for j in range(5):
                if i == j:
                    continue
                loc_i = locations[friend_names[i]]
                loc_j = locations[friend_names[j]]
                travel_time = travel_dict.get((loc_i, loc_j))
                if travel_time is None:
                    continue
                c = Implies(And(i_var == i, j_var == j), s[j] >= e[i] + travel_time)
                solver.add(c)
    
    if solver.check() == sat:
        m = solver.model()
        order_vals = [m.evaluate(order[i]).as_long() for i in range(5)]
        start_times = [m.evaluate(s[i]).as_long() for i in range(5)]
        end_times = [m.evaluate(e[i]).as_long() for i in range(5)]
        
        meetings = []
        for i in range(5):
            start_min = start_times[i]
            end_min = end_times[i]
            start_hour = start_min // 60
            start_minute = start_min % 60
            end_hour = end_min // 60
            end_minute = end_min % 60
            start_str = f"{start_hour:02d}:{start_minute:02d}"
            end_str = f"{end_hour:02d}:{end_minute:02d}"
            meetings.append({
                "friend": friend_names[i],
                "start": start_str,
                "end": end_str
            })
        
        meetings_sorted = sorted(meetings, key=lambda x: x['start'])
        itinerary = []
        for meet in meetings_sorted:
            itinerary.append({
                "action": "meet",
                "person": meet['friend'],
                "start_time": meet['start'],
                "end_time": meet['end']
            })
        
        result = {"itinerary": itinerary}
        print("SOLUTION:")
        print(json.dumps(result, indent=2))
    else:
        print("No feasible schedule found")

if __name__ == "__main__":
    main()