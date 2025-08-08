from z3 import *
import itertools

def build_travel_times():
    return {
        "Richmond District": {"Richmond District": 0, "Chinatown": 20, "Sunset District": 11, "Alamo Square": 13, "Financial District": 22, "North Beach": 17, "Embarcadero": 19, "Presidio": 7, "Golden Gate Park": 9, "Bayview": 27},
        "Chinatown": {"Richmond District": 20, "Chinatown": 0, "Sunset District": 29, "Alamo Square": 17, "Financial District": 5, "North Beach": 3, "Embarcadero": 5, "Presidio": 19, "Golden Gate Park": 23, "Bayview": 20},
        "Sunset District": {"Richmond District": 12, "Chinatown": 30, "Sunset District": 0, "Alamo Square": 17, "Financial District": 30, "North Beach": 28, "Embarcadero": 30, "Presidio": 16, "Golden Gate Park": 11, "Bayview": 22},
        "Alamo Square": {"Richmond District": 11, "Chinatown": 15, "Sunset District": 16, "Alamo Square": 0, "Financial District": 17, "North Beach": 15, "Embarcadero": 16, "Presidio": 17, "Golden Gate Park": 9, "Bayview": 16},
        "Financial District": {"Richmond District": 21, "Chinatown": 5, "Sunset District": 30, "Alamo Square": 17, "Financial District": 0, "North Beach": 7, "Embarcadero": 4, "Presidio": 22, "Golden Gate Park": 23, "Bayview": 19},
        "North Beach": {"Richmond District": 18, "Chinatown": 6, "Sunset District": 27, "Alamo Square": 16, "Financial District": 8, "North Beach": 0, "Embarcadero": 6, "Presidio": 17, "Golden Gate Park": 22, "Bayview": 25},
        "Embarcadero": {"Richmond District": 21, "Chinatown": 7, "Sunset District": 30, "Alamo Square": 19, "Financial District": 5, "North Beach": 5, "Embarcadero": 0, "Presidio": 20, "Golden Gate Park": 25, "Bayview": 21},
        "Presidio": {"Richmond District": 7, "Chinatown": 21, "Sunset District": 15, "Alamo Square": 19, "Financial District": 23, "North Beach": 18, "Embarcadero": 20, "Presidio": 0, "Golden Gate Park": 12, "Bayview": 31},
        "Golden Gate Park": {"Richmond District": 7, "Chinatown": 23, "Sunset District": 10, "Alamo Square": 9, "Financial District": 26, "North Beach": 23, "Embarcadero": 25, "Presidio": 11, "Golden Gate Park": 0, "Bayview": 23},
        "Bayview": {"Richmond District": 25, "Chinatown": 19, "Sunset District": 23, "Alamo Square": 16, "Financial District": 19, "North Beach": 22, "Embarcadero": 19, "Presidio": 32, "Golden Gate Park": 22, "Bayview": 0}
    }

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
    
    travel_times_dict = build_travel_times()
    
    min_duration_arr = [f['min_duration'] for f in friends]
    start_avail_arr = [f['start_avail'] for f in friends]
    end_avail_arr = [f['end_avail'] for f in friends]
    
    initial_travel = []
    for f in friends:
        loc = f['location']
        initial_travel.append(travel_times_dict['Richmond District'][loc])
    
    travel_matrix = []
    for i in range(9):
        loc_i = friends[i]['location']
        row = []
        for j in range(9):
            loc_j = friends[j]['location']
            row.append(travel_times_dict[loc_i][loc_j])
        travel_matrix.append(row)
    
    all_meetings = list(range(9))
    
    for size in range(9, 0, -1):
        for subset in itertools.combinations(all_meetings, size):
            s = Solver()
            n = len(subset)
            order = [Int(f'order_{i}') for i in range(n)]
            s_arr = Array('s_arr', IntSort(), IntSort())
            e_arr = Array('e_arr', IntSort(), IntSort())
            
            Travel = Function('Travel', IntSort(), IntSort(), IntSort())
            InitialTravel = Function('InitialTravel', IntSort(), IntSort())
            
            for i_val in range(9):
                s.add(InitialTravel(i_val) == initial_travel[i_val])
                for j_val in range(9):
                    s.add(Travel(i_val, j_val) == travel_matrix[i_val][j_val])
            
            s.add(Distinct(order))
            for i in range(n):
                s.add(Or([order[i] == idx for idx in subset]))
            
            first = order[0]
            s.add(s_arr[first] >= 540 + InitialTravel(first))
            
            for i in range(1, n):
                prev = order[i-1]
                curr = order[i]
                s.add(s_arr[curr] >= e_arr[prev] + Travel(prev, curr))
            
            for idx in subset:
                s.add(e_arr[idx] - s_arr[idx] >= min_duration_arr[idx])
                s.add(s_arr[idx] >= start_avail_arr[idx])
                s.add(e_arr[idx] <= end_avail_arr[idx])
            
            if s.check() == sat:
                m = s.model()
                order_vals = [m.evaluate(order[i]).as_long() for i in range(n)]
                itinerary_list = []
                for pos in range(n):
                    friend_idx = order_vals[pos]
                    start_val = m.evaluate(s_arr[friend_idx]).as_long()
                    end_val = m.evaluate(e_arr[friend_idx]).as_long()
                    start_hour = start_val // 60
                    start_minute = start_val % 60
                    end_hour = end_val // 60
                    end_minute = end_val % 60
                    start_time = f"{start_hour:02d}:{start_minute:02d}"
                    end_time = f"{end_hour:02d}:{end_minute:02d}"
                    itinerary_list.append({
                        "action": "meet",
                        "person": friends[friend_idx]['name'],
                        "start_time": start_time,
                        "end_time": end_time
                    })
                print('SOLUTION:')
                print({'itinerary': itinerary_list})
                return
                
    print('SOLUTION:')
    print({'itinerary': []})

if __name__ == '__main__':
    main()