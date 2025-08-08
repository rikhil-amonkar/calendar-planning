from z3 import *
import json

def main():
    friends_data = [
        {"name": "Brian", "location": "North Beach", "start_avail": 240, "end_avail": 720, "min_duration": 90},
        {"name": "Richard", "location": "Fisherman's Wharf", "start_avail": 120, "end_avail": 225, "min_duration": 60},
        {"name": "Ashley", "location": "Haight-Ashbury", "start_avail": 360, "end_avail": 690, "min_duration": 90},
        {"name": "Elizabeth", "location": "Nob Hill", "start_avail": 165, "end_avail": 570, "min_duration": 75},
        {"name": "Jessica", "location": "Golden Gate Park", "start_avail": 660, "end_avail": 765, "min_duration": 105},
        {"name": "Deborah", "location": "Union Square", "start_avail": 510, "end_avail": 780, "min_duration": 60},
        {"name": "Kimberly", "location": "Alamo Square", "start_avail": 510, "end_avail": 735, "min_duration": 45},
        {"name": "Kenneth", "location": "Chinatown", "start_avail": 285, "end_avail": 630, "min_duration": 105},
        {"name": "Anthony", "location": "Pacific Heights", "start_avail": 315, "end_avail": 420, "min_duration": 30}
    ]
    
    travel_dict = {
        "Bayview": {
            "North Beach": 22, "Fisherman's Wharf": 25, "Haight-Ashbury": 19, "Nob Hill": 20,
            "Golden Gate Park": 22, "Union Square": 18, "Alamo Square": 16, "Presidio": 32,
            "Chinatown": 19, "Pacific Heights": 23
        },
        "North Beach": {
            "Bayview": 25, "Fisherman's Wharf": 5, "Haight-Ashbury": 18, "Nob Hill": 7,
            "Golden Gate Park": 22, "Union Square": 7, "Alamo Square": 16, "Presidio": 17,
            "Chinatown": 6, "Pacific Heights": 8
        },
        "Fisherman's Wharf": {
            "Bayview": 26, "North Beach": 6, "Haight-Ashbury": 22, "Nob Hill": 11,
            "Golden Gate Park": 25, "Union Square": 13, "Alamo Square": 21, "Presidio": 17,
            "Chinatown": 12, "Pacific Heights": 12
        },
        "Haight-Ashbury": {
            "Bayview": 18, "North Beach": 19, "Fisherman's Wharf": 23, "Nob Hill": 15,
            "Golden Gate Park": 7, "Union Square": 19, "Alamo Square": 5, "Presidio": 15,
            "Chinatown": 19, "Pacific Heights": 12
        },
        "Nob Hill": {
            "Bayview": 19, "North Beach": 8, "Fisherman's Wharf": 10, "Haight-Ashbury": 13,
            "Golden Gate Park": 17, "Union Square": 7, "Alamo Square": 11, "Presidio": 17,
            "Chinatown": 6, "Pacific Heights": 8
        },
        "Golden Gate Park": {
            "Bayview": 23, "North Beach": 23, "Fisherman's Wharf": 24, "Haight-Ashbury": 7,
            "Nob Hill": 20, "Union Square": 22, "Alamo Square": 9, "Presidio": 11,
            "Chinatown": 23, "Pacific Heights": 16
        },
        "Union Square": {
            "Bayview": 15, "North Beach": 10, "Fisherman's Wharf": 15, "Haight-Ashbury": 18,
            "Nob Hill": 9, "Golden Gate Park": 22, "Alamo Square": 15, "Presidio": 24,
            "Chinatown": 7, "Pacific Heights": 15
        },
        "Alamo Square": {
            "Bayview": 16, "North Beach": 15, "Fisherman's Wharf": 19, "Haight-Ashbury": 5,
            "Nob Hill": 11, "Golden Gate Park": 9, "Union Square": 14, "Presidio": 17,
            "Chinatown": 15, "Pacific Heights": 10
        },
        "Presidio": {
            "Bayview": 31, "North Beach": 18, "Fisherman's Wharf": 19, "Haight-Ashbury": 15,
            "Nob Hill": 18, "Golden Gate Park": 12, "Union Square": 22, "Alamo Square": 19,
            "Chinatown": 21, "Pacific Heights": 11
        },
        "Chinatown": {
            "Bayview": 20, "North Beach": 3, "Fisherman's Wharf": 8, "Haight-Ashbury": 19,
            "Nob Hill": 9, "Golden Gate Park": 23, "Union Square": 7, "Alamo Square": 17,
            "Presidio": 19, "Pacific Heights": 10
        },
        "Pacific Heights": {
            "Bayview": 22, "North Beach": 9, "Fisherman's Wharf": 13, "Haight-Ashbury": 11,
            "Nob Hill": 8, "Golden Gate Park": 15, "Union Square": 12, "Alamo Square": 10,
            "Presidio": 11, "Chinatown": 11
        }
    }
    
    s = Optimize()
    n = len(friends_data)
    
    meet = [Bool(f"meet_{i}") for i in range(n)]
    start = [Int(f"start_{i}") for i in range(n)]
    end = [Int(f"end_{i}") for i in range(n)]
    
    for i in range(n):
        friend = friends_data[i]
        s.add(Implies(meet[i], start[i] >= friend["start_avail"]))
        s.add(Implies(meet[i], end[i] == start[i] + friend["min_duration"]))
        s.add(Implies(meet[i], end[i] <= friend["end_avail"]))
        travel_time = travel_dict["Bayview"][friend["location"]]
        s.add(Implies(meet[i], start[i] >= travel_time))
    
    for i in range(n):
        for j in range(i+1, n):
            loc_i = friends_data[i]["location"]
            loc_j = friends_data[j]["location"]
            travel_ij = travel_dict[loc_i][loc_j]
            travel_ji = travel_dict[loc_j][loc_i]
            cond1 = start[i] >= end[j] + travel_ji
            cond2 = start[j] >= end[i] + travel_ij
            s.add(Implies(And(meet[i], meet[j]), Or(cond1, cond2)))
    
    total_meetings = Sum([If(meet[i], 1, 0) for i in range(n)])
    s.maximize(total_meetings)
    
    itinerary = []
    if s.check() == sat:
        m = s.model()
        for i in range(n):
            if m.eval(meet[i]):
                start_val = m.eval(start[i]).as_long()
                end_val = m.eval(end[i]).as_long()
                hours_start = start_val // 60 + 9
                minutes_start = start_val % 60
                start_str = f"{hours_start:02d}:{minutes_start:02d}"
                hours_end = end_val // 60 + 9
                minutes_end = end_val % 60
                end_str = f"{hours_end:02d}:{minutes_end:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": friends_data[i]["name"],
                    "start_time": start_str,
                    "end_time": end_str
                })
        itinerary.sort(key=lambda x: x['start_time'])
    else:
        itinerary = []
    
    result = {"itinerary": itinerary}
    print("SOLUTION:")
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()