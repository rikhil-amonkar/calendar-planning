from z3 import *
import itertools

def build_travel_times():
    travel_times = {
        "Richmond District": {
            "Chinatown": 20,
            "Sunset District": 11,
            "Alamo Square": 13,
            "Financial District": 22,
            "North Beach": 17,
            "Embarcadero": 19,
            "Presidio": 7,
            "Golden Gate Park": 9,
            "Bayview": 27
        },
        "Chinatown": {
            "Richmond District": 20,
            "Sunset District": 29,
            "Alamo Square": 17,
            "Financial District": 5,
            "North Beach": 3,
            "Embarcadero": 5,
            "Presidio": 19,
            "Golden Gate Park": 23,
            "Bayview": 20
        },
        "Sunset District": {
            "Richmond District": 12,
            "Chinatown": 30,
            "Alamo Square": 17,
            "Financial District": 30,
            "North Beach": 28,
            "Embarcadero": 30,
            "Presidio": 16,
            "Golden Gate Park": 11,
            "Bayview": 22
        },
        "Alamo Square": {
            "Richmond District": 11,
            "Chinatown": 15,
            "Sunset District": 16,
            "Financial District": 17,
            "North Beach": 15,
            "Embarcadero": 16,
            "Presidio": 17,
            "Golden Gate Park": 9,
            "Bayview": 16
        },
        "Financial District": {
            "Richmond District": 21,
            "Chinatown": 5,
            "Sunset District": 30,
            "Alamo Square": 17,
            "North Beach": 7,
            "Embarcadero": 4,
            "Presidio": 22,
            "Golden Gate Park": 23,
            "Bayview": 19
        },
        "North Beach": {
            "Richmond District": 18,
            "Chinatown": 6,
            "Sunset District": 27,
            "Alamo Square": 16,
            "Financial District": 8,
            "Embarcadero": 6,
            "Presidio": 17,
            "Golden Gate Park": 22,
            "Bayview": 25
        },
        "Embarcadero": {
            "Richmond District": 21,
            "Chinatown": 7,
            "Sunset District": 30,
            "Alamo Square": 19,
            "Financial District": 5,
            "North Beach": 5,
            "Presidio": 20,
            "Golden Gate Park": 25,
            "Bayview": 21
        },
        "Presidio": {
            "Richmond District": 7,
            "Chinatown": 21,
            "Sunset District": 15,
            "Alamo Square": 19,
            "Financial District": 23,
            "North Beach": 18,
            "Embarcadero": 20,
            "Golden Gate Park": 12,
            "Bayview": 31
        },
        "Golden Gate Park": {
            "Richmond District": 7,
            "Chinatown": 23,
            "Sunset District": 10,
            "Alamo Square": 9,
            "Financial District": 26,
            "North Beach": 23,
            "Embarcadero": 25,
            "Presidio": 11,
            "Bayview": 23
        },
        "Bayview": {
            "Richmond District": 25,
            "Chinatown": 19,
            "Sunset District": 23,
            "Alamo Square": 16,
            "Financial District": 19,
            "North Beach": 22,
            "Embarcadero": 19,
            "Presidio": 32,
            "Golden Gate Park": 22
        }
    }
    return travel_times

def main():
    friends = [
        {"name": "Robert", "location": "Chinatown", "start_avail": 7*60+45, "end_avail": 17*60+30, "min_duration": 120},
        {"name": "David", "location": "Sunset District", "start_avail": 12*60+30, "end_avail": 19*60+45, "min_duration": 45},
        {"name": "Matthew", "location": "Alamo Square", "start_avail": 8*60+45, "end_avail": 13*60+45, "min_duration": 90},
        {"name": "Jessica", "location": "Financial District", "start_avail": 9*60+30, "end_avail": 18*60+45, "min_duration": 45},
        {"name": "Melissa", "location": "North Beach", "start_avail": 7*60+15, "end_avail": 16*60+45, "min_duration": 45},
        {"name": "Mark", "location": "Embarcadero", "start_avail": 15*60+15, "end_avail": 17*60, "min_duration": 45},
        {"name": "Deborah", "location": "Presidio", "start_avail": 19*60, "end_avail": 19*60+45, "min_duration": 45},
        {"name": "Karen", "location": "Golden Gate Park", "start_avail": 19*60+30, "end_avail": 22*60, "min_duration": 120},
        {"name": "Laura", "location": "Bayview", "start_avail": 21*60+15, "end_avail": 22*60+15, "min_duration": 15}
    ]
    
    travel_times = build_travel_times()
    all_meetings = list(range(9))
    
    for size in range(9, 0, -1):
        for subset in itertools.combinations(all_meetings, size):
            s = [Int(f's_{i}') for i in range(9)]
            e = [Int(f'e_{i}') for i in range(9)]
            n = len(subset)
            order = [Int(f'order_{i}') for i in range(n)]
            
            solver = Solver()
            
            for i in range(n):
                solver.add(Or([order[i] == idx for idx in subset]))
            solver.add(Distinct(order))
            
            first = order[0]
            loc0 = friends[first]['location']
            travel_time0 = travel_times['Richmond District'][loc0]
            solver.add(s[first] >= 540 + travel_time0)
            
            for i in range(1, n):
                prev = order[i-1]
                curr = order[i]
                loc_prev = friends[prev]['location']
                loc_curr = friends[curr]['location']
                time_between = travel_times[loc_prev][loc_curr]
                solver.add(s[curr] >= e[prev] + time_between)
                
            for idx in subset:
                solver.add(e[idx] - s[idx] >= friends[idx]['min_duration'])
                solver.add(s[idx] >= friends[idx]['start_avail'])
                solver.add(e[idx] <= friends[idx]['end_avail'])
                
            if solver.check() == sat:
                model = solver.model()
                schedule_order = []
                for i in range(n):
                    idx_val = model[order[i]].as_long()
                    schedule_order.append(idx_val)
                
                itinerary_list = []
                for idx in schedule_order:
                    start_val = model[s[idx]].as_long()
                    end_val = model[e[idx]].as_long()
                    start_hour = start_val // 60
                    start_minute = start_val % 60
                    end_hour = end_val // 60
                    end_minute = end_val % 60
                    start_str = f"{start_hour:02d}:{start_minute:02d}"
                    end_str = f"{end_hour:02d}:{end_minute:02d}"
                    itinerary_list.append({
                        "action": "meet",
                        "person": friends[idx]['name'],
                        "start_time": start_str,
                        "end_time": end_str
                    })
                
                print('SOLUTION:')
                print({'itinerary': itinerary_list})
                return
                
    print('SOLUTION:')
    print({'itinerary': []})

if __name__ == '__main__':
    main()