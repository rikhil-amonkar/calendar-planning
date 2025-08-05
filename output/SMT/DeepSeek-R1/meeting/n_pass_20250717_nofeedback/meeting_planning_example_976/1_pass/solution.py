import json
from z3 import *

def main():
    friends = [
        ("Stephanie", "Presidio", 450, 615, 60),    # 7:30 AM to 10:15 AM
        ("Brian", "Marina District", 735, 1080, 60), # 12:15 PM to 6:00 PM
        ("Thomas", "Fisherman's Wharf", 810, 1140, 30), # 1:30 PM to 7:00 PM
        ("Nancy", "North Beach", 885, 1200, 15),    # 2:45 PM to 8:00 PM
        ("Jessica", "Nob Hill", 990, 1125, 120),    # 4:30 PM to 6:45 PM
        ("Mary", "Union Square", 1005, 1290, 60),    # 4:45 PM to 9:30 PM
        ("Charles", "The Castro", 990, 1320, 105),  # 4:30 PM to 10:00 PM
        ("Matthew", "Bayview", 1155, 1320, 120),    # 7:15 PM to 10:00 PM
        ("Karen", "Chinatown", 1155, 1275, 90),     # 7:15 PM to 9:15 PM
        ("Sarah", "Alamo Square", 1200, 1305, 105)  # 8:00 PM to 9:45 PM
    ]
    
    travel_dict = {
        ("Embarcadero", "Bayview"): 21,
        ("Embarcadero", "Chinatown"): 7,
        ("Embarcadero", "Alamo Square"): 19,
        ("Embarcadero", "Nob Hill"): 10,
        ("Embarcadero", "Presidio"): 20,
        ("Embarcadero", "Union Square"): 10,
        ("Embarcadero", "The Castro"): 25,
        ("Embarcadero", "North Beach"): 5,
        ("Embarcadero", "Fisherman's Wharf"): 6,
        ("Embarcadero", "Marina District"): 12,
        ("Bayview", "Embarcadero"): 19,
        ("Bayview", "Chinatown"): 19,
        ("Bayview", "Alamo Square"): 16,
        ("Bayview", "Nob Hill"): 20,
        ("Bayview", "Presidio"): 32,
        ("Bayview", "Union Square"): 18,
        ("Bayview", "The Castro"): 19,
        ("Bayview", "North Beach"): 22,
        ("Bayview", "Fisherman's Wharf"): 25,
        ("Bayview", "Marina District"): 27,
        ("Chinatown", "Embarcadero"): 5,
        ("Chinatown", "Bayview"): 20,
        ("Chinatown", "Alamo Square"): 17,
        ("Chinatown", "Nob Hill"): 9,
        ("Chinatown", "Presidio"): 19,
        ("Chinatown", "Union Square"): 7,
        ("Chinatown", "The Castro"): 22,
        ("Chinatown", "North Beach"): 3,
        ("Chinatown", "Fisherman's Wharf"): 8,
        ("Chinatown", "Marina District"): 12,
        ("Alamo Square", "Embarcadero"): 16,
        ("Alamo Square", "Bayview"): 16,
        ("Alamo Square", "Chinatown"): 15,
        ("Alamo Square", "Nob Hill"): 11,
        ("Alamo Square", "Presidio"): 17,
        ("Alamo Square", "Union Square"): 14,
        ("Alamo Square", "The Castro"): 8,
        ("Alamo Square", "North Beach"): 15,
        ("Alamo Square", "Fisherman's Wharf"): 19,
        ("Alamo Square", "Marina District"): 15,
        ("Nob Hill", "Embarcadero"): 9,
        ("Nob Hill", "Bayview"): 19,
        ("Nob Hill", "Chinatown"): 6,
        ("Nob Hill", "Alamo Square"): 11,
        ("Nob Hill", "Presidio"): 17,
        ("Nob Hill", "Union Square"): 7,
        ("Nob Hill", "The Castro"): 17,
        ("Nob Hill", "North Beach"): 8,
        ("Nob Hill", "Fisherman's Wharf"): 10,
        ("Nob Hill", "Marina District"): 11,
        ("Presidio", "Embarcadero"): 20,
        ("Presidio", "Bayview"): 31,
        ("Presidio", "Chinatown"): 21,
        ("Presidio", "Alamo Square"): 19,
        ("Presidio", "Nob Hill"): 18,
        ("Presidio", "Union Square"): 22,
        ("Presidio", "The Castro"): 21,
        ("Presidio", "North Beach"): 18,
        ("Presidio", "Fisherman's Wharf"): 19,
        ("Presidio", "Marina District"): 11,
        ("Union Square", "Embarcadero"): 11,
        ("Union Square", "Bayview"): 15,
        ("Union Square", "Chinatown"): 7,
        ("Union Square", "Alamo Square"): 15,
        ("Union Square", "Nob Hill"): 9,
        ("Union Square", "Presidio"): 24,
        ("Union Square", "The Castro"): 17,
        ("Union Square", "North Beach"): 10,
        ("Union Square", "Fisherman's Wharf"): 15,
        ("Union Square", "Marina District"): 18,
        ("The Castro", "Embarcadero"): 22,
        ("The Castro", "Bayview"): 19,
        ("The Castro", "Chinatown"): 22,
        ("The Castro", "Alamo Square"): 8,
        ("The Castro", "Nob Hill"): 16,
        ("The Castro", "Presidio"): 20,
        ("The Castro", "Union Square"): 19,
        ("The Castro", "North Beach"): 20,
        ("The Castro", "Fisherman's Wharf"): 24,
        ("The Castro", "Marina District"): 21,
        ("North Beach", "Embarcadero"): 6,
        ("North Beach", "Bayview"): 25,
        ("North Beach", "Chinatown"): 6,
        ("North Beach", "Alamo Square"): 16,
        ("North Beach", "Nob Hill"): 7,
        ("North Beach", "Presidio"): 17,
        ("North Beach", "Union Square"): 7,
        ("North Beach", "The Castro"): 23,
        ("North Beach", "Fisherman's Wharf"): 5,
        ("North Beach", "Marina District"): 9,
        ("Fisherman's Wharf", "Embarcadero"): 8,
        ("Fisherman's Wharf", "Bayview"): 26,
        ("Fisherman's Wharf", "Chinatown"): 12,
        ("Fisherman's Wharf", "Alamo Square"): 21,
        ("Fisherman's Wharf", "Nob Hill"): 11,
        ("Fisherman's Wharf", "Presidio"): 17,
        ("Fisherman's Wharf", "Union Square"): 13,
        ("Fisherman's Wharf", "The Castro"): 27,
        ("Fisherman's Wharf", "North Beach"): 6,
        ("Fisherman's Wharf", "Marina District"): 9,
        ("Marina District", "Embarcadero"): 14,
        ("Marina District", "Bayview"): 27,
        ("Marina District", "Chinatown"): 15,
        ("Marina District", "Alamo Square"): 15,
        ("Marina District", "Nob Hill"): 12,
        ("Marina District", "Presidio"): 10,
        ("Marina District", "Union Square"): 16,
        ("Marina District", "The Castro"): 22,
        ("Marina District", "North Beach"): 11,
        ("Marina District", "Fisherman's Wharf"): 10
    }

    n = len(friends)
    meet = [Bool(f'meet_{i}') for i in range(n)]
    start = [Int(f'start_{i}') for i in range(n)]
    end = [Int(f'end_{i}') for i in range(n)]

    opt = Optimize()
    
    for i in range(n):
        name, loc, avail_start, avail_end, min_dur = friends[i]
        opt.add(Implies(meet[i], And(start[i] >= avail_start, end[i] <= avail_end, end[i] - start[i] >= min_dur)))
        tt_from_emb = travel_dict[("Embarcadero", loc)]
        opt.add(Implies(meet[i], start[i] >= 540 + tt_from_emb))

    for i in range(n):
        for j in range(i+1, n):
            name_i, loc_i, _, _, _ = friends[i]
            name_j, loc_j, _, _, _ = friends[j]
            tt_ij = travel_dict.get((loc_i, loc_j), None)
            tt_ji = travel_dict.get((loc_j, loc_i), None)
            if tt_ij is None or tt_ji is None:
                continue
            opt.add(Implies(And(meet[i], meet[j]), Or(end[i] + tt_ij <= start[j], end[j] + tt_ji <= start[i])))
    
    num_meet = Sum([If(meet[i], 1, 0) for i in range(n)])
    opt.maximize(num_meet)
    
    result = []
    if opt.check() == sat:
        m = opt.model()
        for i in range(n):
            if m.eval(meet[i]):
                name, _, _, _, _ = friends[i]
                start_val = m.eval(start[i]).as_long()
                end_val = m.eval(end[i]).as_long()
                start_h = start_val // 60
                start_m = start_val % 60
                end_h = end_val // 60
                end_m = end_val % 60
                start_str = f"{start_h:02d}:{start_m:02d}"
                end_str = f"{end_h:02d}:{end_m:02d}"
                result.append({"action": "meet", "person": name, "start_time": start_str, "end_time": end_str})
        result.sort(key=lambda x: (int(x['start_time'][:2]) * 60 + int(x['start_time'][3:5])))
    
    print("SOLUTION:")
    print(json.dumps({"itinerary": result}))

if __name__ == "__main__":
    main()