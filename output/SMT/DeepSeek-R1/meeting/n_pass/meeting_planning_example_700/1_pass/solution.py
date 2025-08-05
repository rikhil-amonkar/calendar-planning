from z3 import *

def main():
    friends = [
        ("Helen", "North Beach", 120, 195, 45),
        ("Emily", "Fisherman's Wharf", 435, 600, 30),
        ("Barbara", "Alamo Square", 480, 600, 120),
        ("Mark", "Marina District", 555, 645, 75),
        ("Mary", "Nob Hill", 510, 600, 45),
        ("Laura", "Sunset District", 600, 735, 75),
        ("Michelle", "Golden Gate Park", 660, 720, 15)
    ]
    
    travel_times = {
        ("Presidio", "North Beach"): 18,
        ("Presidio", "Fisherman's Wharf"): 19,
        ("Presidio", "Alamo Square"): 19,
        ("Presidio", "Marina District"): 11,
        ("Presidio", "Nob Hill"): 18,
        ("Presidio", "Sunset District"): 15,
        ("Presidio", "Golden Gate Park"): 12,
        ("North Beach", "Presidio"): 17,
        ("North Beach", "Fisherman's Wharf"): 5,
        ("North Beach", "Alamo Square"): 16,
        ("North Beach", "Marina District"): 9,
        ("North Beach", "Nob Hill"): 8,
        ("North Beach", "Sunset District"): 27,
        ("North Beach", "Golden Gate Park"): 22,
        ("Fisherman's Wharf", "Presidio"): 17,
        ("Fisherman's Wharf", "North Beach"): 6,
        ("Fisherman's Wharf", "Alamo Square"): 21,
        ("Fisherman's Wharf", "Marina District"): 9,
        ("Fisherman's Wharf", "Nob Hill"): 11,
        ("Fisherman's Wharf", "Sunset District"): 27,
        ("Fisherman's Wharf", "Golden Gate Park"): 24,
        ("Alamo Square", "Presidio"): 17,
        ("Alamo Square", "North Beach"): 15,
        ("Alamo Square", "Fisherman's Wharf"): 19,
        ("Alamo Square", "Marina District"): 15,
        ("Alamo Square", "Nob Hill"): 11,
        ("Alamo Square", "Sunset District"): 16,
        ("Alamo Square", "Golden Gate Park"): 9,
        ("Marina District", "Presidio"): 10,
        ("Marina District", "North Beach"): 11,
        ("Marina District", "Fisherman's Wharf"): 10,
        ("Marina District", "Alamo Square"): 15,
        ("Marina District", "Nob Hill"): 12,
        ("Marina District", "Sunset District"): 19,
        ("Marina District", "Golden Gate Park"): 18,
        ("Nob Hill", "Presidio"): 17,
        ("Nob Hill", "North Beach"): 8,
        ("Nob Hill", "Fisherman's Wharf"): 10,
        ("Nob Hill", "Alamo Square"): 11,
        ("Nob Hill", "Marina District"): 11,
        ("Nob Hill", "Sunset District"): 24,
        ("Nob Hill", "Golden Gate Park"): 17,
        ("Sunset District", "Presidio"): 16,
        ("Sunset District", "North Beach"): 28,
        ("Sunset District", "Fisherman's Wharf"): 29,
        ("Sunset District", "Alamo Square"): 17,
        ("Sunset District", "Marina District"): 21,
        ("Sunset District", "Nob Hill"): 27,
        ("Sunset District", "Golden Gate Park"): 11,
        ("Golden Gate Park", "Presidio"): 11,
        ("Golden Gate Park", "North Beach"): 23,
        ("Golden Gate Park", "Fisherman's Wharf"): 24,
        ("Golden Gate Park", "Alamo Square"): 9,
        ("Golden Gate Park", "Marina District"): 16,
        ("Golden Gate Park", "Nob Hill"): 20,
        ("Golden Gate Park", "Sunset District"): 10,
    }
    
    n = len(friends)
    opt = Optimize()
    
    attend = [Bool(f'attend_{i}') for i in range(n)]
    start = [Real(f'start_{i}') for i in range(n)]
    end = [Real(f'end_{i}') for i in range(n)]
    before = {}
    for i in range(n):
        for j in range(n):
            if i != j:
                before[(i,j)] = Bool(f'before_{i}_{j}')
    
    for i in range(n):
        name, loc, a_start, a_end, dur = friends[i]
        opt.add(Implies(attend[i], And(start[i] >= a_start, start[i] <= a_end - dur, end[i] == start[i] + dur)))
        tt_to_loc = travel_times[("Presidio", loc)]
        opt.add(Implies(attend[i], start[i] >= tt_to_loc))
    
    for i in range(n):
        for j in range(n):
            if i == j:
                continue
            opt.add(Implies(And(attend[i], attend[j]), 
                    Or(before[(i,j)], before[(j,i)])))
            opt.add(Implies(And(attend[i], attend[j]), 
                    before[(i,j)] == Not(before[(j,i)])))
    
    for i in range(n):
        for j in range(n):
            if i == j:
                continue
            name_i, loc_i, _, _, _ = friends[i]
            name_j, loc_j, _, _, _ = friends[j]
            tt_ij = travel_times.get((loc_i, loc_j))
            if tt_ij is None:
                tt_ij = 1000
            opt.add(Implies(And(attend[i], attend[j], before[(i,j)]), 
                           end[i] + tt_ij <= start[j]))
    
    num_meetings = Sum([If(attend[i], 1, 0) for i in range(n)])
    opt.maximize(num_meetings)
    
    if opt.check() == sat:
        m = opt.model()
        itinerary = []
        for i in range(n):
            if is_true(m[attend[i]]):
                name = friends[i][0]
                s_val = m[start[i]]
                if isinstance(s_val, RatNumRef):
                    s_val = s_val.as_fraction()
                else:
                    s_val = m[s_val].as_fraction() if isinstance(m[s_val], RatNumRef) else float(str(m[s_val]))
                e_val = m[end[i]]
                if isinstance(e_val, RatNumRef):
                    e_val = e_val.as_fraction()
                else:
                    e_val = m[e_val].as_fraction() if isinstance(m[e_val], RatNumRef) else float(str(m[e_val]))
                s_minutes = int(s_val)
                e_minutes = int(e_val)
                s_hour = 9 + s_minutes // 60
                s_minute = s_minutes % 60
                e_hour = 9 + e_minutes // 60
                e_minute = e_minutes % 60
                start_str = f"{s_hour:02d}:{s_minute:02d}"
                end_str = f"{e_hour:02d}:{e_minute:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": start_str,
                    "end_time": end_str
                })
        itinerary.sort(key=lambda x: x['start_time'])
        result = {"itinerary": itinerary}
        print(result)
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()