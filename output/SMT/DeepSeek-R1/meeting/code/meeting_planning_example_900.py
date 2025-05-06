from z3 import *

def main():
    # Friends data: name, location, start (min), end (min), duration (min)
    friends = [
        ("Virtual", "Richmond District", 9*60, 9*60, 0),
        ("Matthew", "The Castro", 16*60+30, 20*60, 45),
        ("Rebecca", "Nob Hill", 15*60+15, 19*60+15, 105),
        ("Brian", "Marina District", 14*60+15, 22*60, 30),
        ("Emily", "Pacific Heights", 11*60+15, 19*60+45, 15),
        ("Karen", "Haight-Ashbury", 11*60+45, 17*60+30, 30),
        ("Stephanie", "Mission District", 13*60, 15*60+45, 75),
        ("James", "Chinatown", 14*60+30, 19*60, 120),
        ("Steven", "Russian Hill", 14*60, 20*60, 30),
        ("Elizabeth", "Alamo Square", 13*60, 17*60+15, 120),
        ("William", "Bayview", 18*60+15, 20*60+15, 90)
    ]
    
    # Travel times matrix
    travel = {
        "Richmond District": {
            "The Castro": 16, "Nob Hill": 17, "Marina District": 9, "Pacific Heights": 10,
            "Haight-Ashbury": 10, "Mission District": 20, "Chinatown": 20, "Russian Hill": 13,
            "Alamo Square": 13, "Bayview": 27
        },
        "The Castro": {
            "Richmond District": 16, "Nob Hill": 16, "Marina District": 21, "Pacific Heights": 16,
            "Haight-Ashbury": 6, "Mission District": 7, "Chinatown": 22, "Russian Hill": 18,
            "Alamo Square": 8, "Bayview": 19
        },
        "Nob Hill": {
            "Richmond District": 14, "The Castro": 17, "Marina District": 11, "Pacific Heights": 8,
            "Haight-Ashbury": 13, "Mission District": 13, "Chinatown": 6, "Russian Hill": 5,
            "Alamo Square": 11, "Bayview": 19
        },
        "Marina District": {
            "Richmond District": 11, "The Castro": 22, "Nob Hill": 12, "Pacific Heights": 7,
            "Haight-Ashbury": 16, "Mission District": 20, "Chinatown": 15, "Russian Hill": 8,
            "Alamo Square": 15, "Bayview": 27
        },
        "Pacific Heights": {
            "Richmond District": 12, "The Castro": 16, "Nob Hill": 8, "Marina District": 6,
            "Haight-Ashbury": 11, "Mission District": 15, "Chinatown": 11, "Russian Hill": 7,
            "Alamo Square": 10, "Bayview": 22
        },
        "Haight-Ashbury": {
            "Richmond District": 10, "The Castro": 6, "Nob Hill": 15, "Marina District": 17,
            "Pacific Heights": 12, "Mission District": 11, "Chinatown": 19, "Russian Hill": 17,
            "Alamo Square": 5, "Bayview": 18
        },
        "Mission District": {
            "Richmond District": 20, "The Castro": 7, "Nob Hill": 12, "Marina District": 19,
            "Pacific Heights": 16, "Haight-Ashbury": 12, "Chinatown": 16, "Russian Hill": 15,
            "Alamo Square": 11, "Bayview": 14
        },
        "Chinatown": {
            "Richmond District": 20, "The Castro": 22, "Nob Hill": 9, "Marina District": 12,
            "Pacific Heights": 10, "Haight-Ashbury": 19, "Mission District": 17, "Russian Hill": 7,
            "Alamo Square": 17, "Bayview": 20
        },
        "Russian Hill": {
            "Richmond District": 14, "The Castro": 21, "Nob Hill": 5, "Marina District": 7,
            "Pacific Heights": 7, "Haight-Ashbury": 17, "Mission District": 16, "Chinatown": 9,
            "Alamo Square": 15, "Bayview": 23
        },
        "Alamo Square": {
            "Richmond District": 11, "The Castro": 8, "Nob Hill": 11, "Marina District": 15,
            "Pacific Heights": 10, "Haight-Ashbury": 5, "Mission District": 10, "Chinatown": 15,
            "Russian Hill": 13, "Bayview": 16
        },
        "Bayview": {
            "Richmond District": 25, "The Castro": 19, "Nob Hill": 20, "Marina District": 27,
            "Pacific Heights": 23, "Haight-Ashbury": 19, "Mission District": 13, "Chinatown": 19,
            "Russian Hill": 23, "Alamo Square": 16
        }
    }
    
    s = Optimize()
    
    # Friend variables: visited, arrival, departure
    friend_vars = []
    for name, loc, start, end, dur in friends:
        visited = Bool(f'v_{name}')
        arrive = Int(f'a_{name}')
        depart = Int(f'd_{name}')
        friend_vars.append( (name, loc, start, end, dur, visited, arrive, depart) )
    
    # Constraints for each friend's availability and duration
    for name, loc, start, end, dur, v, a, d in friend_vars:
        if name == "Virtual":
            s.add(v == True)
            s.add(a == 9*60)
            s.add(d == 9*60)
        else:
            s.add(Implies(v, And(a >= start, d <= end, d >= a + dur)))
    
    # Ordering and travel time constraints between friends
    B = {}
    for i, (name_i, loc_i, _, _, _, vi, ai, di) in enumerate(friend_vars):
        for j, (name_j, loc_j, _, _, _, vj, aj, dj) in enumerate(friend_vars):
            if i != j:
                b = Bool(f'b_{name_i}_{name_j}')
                B[(i,j)] = b
                # If both visited, one must come before the other
                s.add(Implies(And(vi, vj), Or(b, B[(j,i)])))
                # If i is before j, j's arrival >= i's departure + travel time
                s.add(Implies(And(b, vi, vj), aj >= di + travel[loc_i][loc_j]))
                s.add(Implies(b, Not(B[(j,i)])))
    
    # Maximize number of friends visited (excluding Virtual)
    total = Sum([If(v, 1, 0) for (name, *_) in friend_vars if name != "Virtual"])
    s.maximize(total)
    
    if s.check() == sat:
        m = s.model()
        print("Optimal schedule:")
        for name, _, _, _, _, v, a, d in friend_vars:
            if name == "Virtual":
                continue
            if m.eval(v):
                a_val = m.eval(a).as_long()
                d_val = m.eval(d).as_long()
                print(f"{name}: {a_val//60:02}:{a_val%60:02} - {d_val//60:02}:{d_val%60:02}")
    else:
        print("No valid schedule found.")

if __name__ == "__main__":
    main()