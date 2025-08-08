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

    n_real = len(friends)
    n_total = n_real + 1  # including dummy meeting at index0

    # Create variables: for the dummy meeting (index0) we don't need a boolean because it's fixed.
    start = [Int(f'start_{i}') for i in range(n_total)]
    end = [Int(f'end_{i}') for i in range(n_total)]
    meet = [Bool(f'meet_{i}') for i in range(n_total)]
    # For the real meetings (indices 1 to n_real), we have booleans. The dummy meeting (index0) is always present.

    s = Optimize()

    # Dummy meeting: at Embarcadero, starts and ends at 540 (9:00 AM)
    s.add(start[0] == 540, end[0] == 540)
    s.add(meet[0] == True)  # dummy is always met, but we won't count it

    # For real meetings (indices 1 to n_real)
    for i in range(1, n_total):
        idx = i - 1  # index in friends list
        name, loc, avail_start, avail_end, min_dur = friends[idx]
        # If we meet this friend, then constraints on time and duration
        s.add(Implies(meet[i], 
                     And(start[i] >= avail_start, 
                         end[i] <= avail_end, 
                         end[i] - start[i] >= min_dur,
                         start[i] >= 0, end[i] >= 0  # non-negative
                     )))

    # Travel constraints: for every pair (i, j) with i < j
    for i in range(n_total):
        for j in range(i+1, n_total):
            if i == 0:  # dummy meeting (Embarcadero)
                # j is a real meeting (index>=1)
                loc_j = friends[j-1][1]  # location of meeting j
                tt = travel_dict[("Embarcadero", loc_j)]
                # If meeting j is met, then start_j >= end_i (540) + travel time
                s.add(Implies(meet[j], start[j] >= end[i] + tt))
            else:
                # both i and j are real meetings (i>=1, j>=1)
                loc_i = friends[i-1][1]
                loc_j = friends[j-1][1]
                tt_ij = travel_dict.get((loc_i, loc_j))
                tt_ji = travel_dict.get((loc_j, loc_i))
                if tt_ij is None or tt_ji is None:
                    # This should not happen, but skip if missing
                    continue
                # If both meetings i and j are met, then either:
                #   end_i + travel(i->j) <= start_j
                #   OR
                #   end_j + travel(j->i) <= start_i
                s.add(Implies(And(meet[i], meet[j]),
                              Or(end[i] + tt_ij <= start[j], 
                                 end[j] + tt_ji <= start[i])))

    # Objective: maximize the number of real meetings
    s.maximize(Sum([If(meet[i], 1, 0) for i in range(1, n_total)]))

    result = []
    if s.check() == sat:
        m = s.model()
        # Extract the meetings that are met
        for i in range(1, n_total):
            if m.eval(meet[i]):
                idx = i - 1
                name, _, _, _, _ = friends[idx]
                start_val = m.eval(start[i]).as_long()
                end_val = m.eval(end[i]).as_long()
                start_h = start_val // 60
                start_m = start_val % 60
                end_h = end_val // 60
                end_m = end_val % 60
                start_str = f"{start_h:02d}:{start_m:02d}"
                end_str = f"{end_h:02d}:{end_m:02d}"
                result.append({"action": "meet", "person": name, "start_time": start_str, "end_time": end_str})
        # Sort by start time
        result.sort(key=lambda x: (int(x['start_time'][:2]) * 60 + int(x['start_time'][3:5]))
    else:
        # If no solution found, return empty list
        result = []

    print("SOLUTION:")
    print(json.dumps({"itinerary": result}))

if __name__ == "__main__":
    main()