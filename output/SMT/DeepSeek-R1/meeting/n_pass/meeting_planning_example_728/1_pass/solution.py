from z3 import *
import json

def main():
    friends = [
        ("Karen", "Mission District", 30, (14*60+15, 22*60)),
        ("Richard", "Fisherman's Wharf", 30, (14*60+30, 17*60+30)),
        ("Robert", "Presidio", 60, (21*60+45, 22*60+45)),
        ("Joseph", "Union Square", 120, (11*60+45, 14*60+45)),
        ("Helen", "Sunset District", 105, (14*60+45, 20*60+45)),
        ("Elizabeth", "Financial District", 75, (10*60, 12*60+45)),
        ("Kimberly", "Haight-Ashbury", 105, (14*60+15, 17*60+30)),
        ("Ashley", "Russian Hill", 45, (11*60+30, 21*60+30))
    ]
    
    travel = {
        ("Marina District", "Mission District"): 20,
        ("Marina District", "Fisherman's Wharf"): 10,
        ("Marina District", "Presidio"): 10,
        ("Marina District", "Union Square"): 16,
        ("Marina District", "Sunset District"): 19,
        ("Marina District", "Financial District"): 17,
        ("Marina District", "Haight-Ashbury"): 16,
        ("Marina District", "Russian Hill"): 8,
        ("Mission District", "Marina District"): 19,
        ("Mission District", "Fisherman's Wharf"): 22,
        ("Mission District", "Presidio"): 25,
        ("Mission District", "Union Square"): 15,
        ("Mission District", "Sunset District"): 24,
        ("Mission District", "Financial District"): 15,
        ("Mission District", "Haight-Ashbury"): 12,
        ("Mission District", "Russian Hill"): 15,
        ("Fisherman's Wharf", "Marina District"): 9,
        ("Fisherman's Wharf", "Mission District"): 22,
        ("Fisherman's Wharf", "Presidio"): 17,
        ("Fisherman's Wharf", "Union Square"): 13,
        ("Fisherman's Wharf", "Sunset District"): 27,
        ("Fisherman's Wharf", "Financial District"): 11,
        ("Fisherman's Wharf", "Haight-Ashbury"): 22,
        ("Fisherman's Wharf", "Russian Hill"): 7,
        ("Presidio", "Marina District"): 11,
        ("Presidio", "Mission District"): 26,
        ("Presidio", "Fisherman's Wharf"): 19,
        ("Presidio", "Union Square"): 22,
        ("Presidio", "Sunset District"): 15,
        ("Presidio", "Financial District"): 23,
        ("Presidio", "Haight-Ashbury"): 15,
        ("Presidio", "Russian Hill"): 14,
        ("Union Square", "Marina District"): 18,
        ("Union Square", "Mission District"): 14,
        ("Union Square", "Fisherman's Wharf"): 15,
        ("Union Square", "Presidio"): 24,
        ("Union Square", "Sunset District"): 27,
        ("Union Square", "Financial District"): 9,
        ("Union Square", "Haight-Ashbury"): 18,
        ("Union Square", "Russian Hill"): 13,
        ("Sunset District", "Marina District"): 21,
        ("Sunset District", "Mission District"): 25,
        ("Sunset District", "Fisherman's Wharf"): 29,
        ("Sunset District", "Presidio"): 16,
        ("Sunset District", "Union Square"): 30,
        ("Sunset District", "Financial District"): 30,
        ("Sunset District", "Haight-Ashbury"): 15,
        ("Sunset District", "Russian Hill"): 24,
        ("Financial District", "Marina District"): 15,
        ("Financial District", "Mission District"): 17,
        ("Financial District", "Fisherman's Wharf"): 10,
        ("Financial District", "Presidio"): 22,
        ("Financial District", "Union Square"): 9,
        ("Financial District", "Sunset District"): 30,
        ("Financial District", "Haight-Ashbury"): 19,
        ("Financial District", "Russian Hill"): 11,
        ("Haight-Ashbury", "Marina District"): 17,
        ("Haight-Ashbury", "Mission District"): 11,
        ("Haight-Ashbury", "Fisherman's Wharf"): 23,
        ("Haight-Ashbury", "Presidio"): 15,
        ("Haight-Ashbury", "Union Square"): 19,
        ("Haight-Ashbury", "Sunset District"): 15,
        ("Haight-Ashbury", "Financial District"): 21,
        ("Haight-Ashbury", "Russian Hill"): 17,
        ("Russian Hill", "Marina District"): 7,
        ("Russian Hill", "Mission District"): 16,
        ("Russian Hill", "Fisherman's Wharf"): 7,
        ("Russian Hill", "Presidio"): 14,
        ("Russian Hill", "Union Square"): 10,
        ("Russian Hill", "Sunset District"): 23,
        ("Russian Hill", "Financial District"): 11,
        ("Russian Hill", "Haight-Ashbury"): 17
    }
    
    s = Solver()
    n = len(friends)
    O = [Int(f'O_{i}') for i in range(n)]
    S = [Int(f'S_{i}') for i in range(n)]
    
    s.add([And(O[i] >= 1, O[i] <= n) for i in range(n)])
    s.add(Distinct(O))
    
    for i in range(n):
        name, district, dur, (start_min, end_min) = friends[i]
        s.add(S[i] >= start_min)
        s.add(S[i] <= end_min - dur)
    
    for i in range(n):
        name, district, dur, window = friends[i]
        s.add(Implies(O[i] == 1, S[i] >= 540 + travel[("Marina District", district)]))
    
    for i in range(n):
        name_i, district_i, dur_i, window_i = friends[i]
        for j in range(n):
            if i == j:
                continue
            name_j, district_j, dur_j, window_j = friends[j]
            s.add(Implies(O[i] < O[j], S[i] + dur_i + travel[(district_i, district_j)] <= S[j]))
    
    if s.check() == sat:
        m = s.model()
        order_vals = [m.evaluate(O[i]).as_long() for i in range(n)]
        start_vals = [m.evaluate(S[i]).as_long() for i in range(n)]
        
        schedule = []
        for i in range(n):
            name, district, dur, window = friends[i]
            start_min = start_vals[i]
            end_min = start_min + dur
            start_h = start_min // 60
            start_m = start_min % 60
            end_h = end_min // 60
            end_m = end_min % 60
            start_time = f"{start_h:02d}:{start_m:02d}"
            end_time = f"{end_h:02d}:{end_m:02d}"
            schedule.append((order_vals[i], name, start_time, end_time))
        
        schedule.sort(key=lambda x: x[0])
        itinerary = [{"action": "meet", "person": name, "start_time": start, "end_time": end} 
                     for (order, name, start, end) in schedule]
        
        print("SOLUTION:")
        print(json.dumps({"itinerary": itinerary}))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()