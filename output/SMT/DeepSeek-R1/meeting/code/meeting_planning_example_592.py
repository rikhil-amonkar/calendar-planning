from z3 import *

def main():
    # Friends data: name, location, start (min), end (min), duration (min)
    friends = [
        ("Virtual", "North Beach", 540, 540, 0),
        ("James", "Pacific Heights", 20*60, 22*60, 120),
        ("Robert", "Chinatown", 12*60+15, 16*60+45, 90),
        ("Jeffrey", "Union Square", 9*60+30, 15*60+30, 120),
        ("Carol", "Mission District", 18*60+15, 21*60+15, 15),
        ("Mark", "Golden Gate Park", 11*60+30, 17*60+45, 15),
        ("Sandra", "Nob Hill", 8*60, 15*60+30, 15)
    ]
    
    # Travel times matrix
    travel = {
        "North Beach": {
            "Pacific Heights": 8,
            "Chinatown": 6,
            "Union Square": 7,
            "Mission District": 18,
            "Golden Gate Park": 22,
            "Nob Hill": 7
        },
        "Pacific Heights": {
            "North Beach": 9,
            "Chinatown": 11,
            "Union Square": 12,
            "Mission District": 15,
            "Golden Gate Park": 15,
            "Nob Hill": 8
        },
        "Chinatown": {
            "North Beach": 3,
            "Pacific Heights": 10,
            "Union Square": 7,
            "Mission District": 18,
            "Golden Gate Park": 23,
            "Nob Hill": 8
        },
        "Union Square": {
            "North Beach": 10,
            "Pacific Heights": 15,
            "Chinatown": 7,
            "Mission District": 14,
            "Golden Gate Park": 22,
            "Nob Hill": 9
        },
        "Mission District": {
            "North Beach": 17,
            "Pacific Heights": 16,
            "Chinatown": 16,
            "Union Square": 15,
            "Golden Gate Park": 17,
            "Nob Hill": 12
        },
        "Golden Gate Park": {
            "North Beach": 24,
            "Pacific Heights": 16,
            "Chinatown": 23,
            "Union Square": 22,
            "Mission District": 17,
            "Nob Hill": 20
        },
        "Nob Hill": {
            "North Beach": 8,
            "Pacific Heights": 8,
            "Chinatown": 6,
            "Union Square": 7,
            "Mission District": 13,
            "Golden Gate Park": 17
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
            s.add(a == 540)
            s.add(d == 540)
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