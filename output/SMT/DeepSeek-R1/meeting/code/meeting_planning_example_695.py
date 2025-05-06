from z3 import *

def main():
    # Friends data: name, location, start (min), end (min), duration (min)
    friends = [
        ("Virtual", "Bayview", 9*60, 9*60, 0),
        ("Paul", "Nob Hill", 16*60+15, 21*60+15, 60),
        ("Carol", "Union Square", 18*60, 20*60+15, 120),
        ("Patricia", "Chinatown", 20*60, 21*60+30, 75),
        ("Karen", "The Castro", 17*60, 19*60, 45),
        ("Nancy", "Presidio", 11*60+45, 22*60, 30),
        ("Jeffrey", "Pacific Heights", 20*60, 20*60+45, 45),
        ("Matthew", "Russian Hill", 15*60+45, 21*60+45, 75)
    ]
    
    # Travel times matrix
    travel = {
        "Bayview": {
            "Nob Hill": 20, "Union Square": 17, "Chinatown": 18, "The Castro": 20,
            "Presidio": 31, "Pacific Heights": 23, "Russian Hill": 23
        },
        "Nob Hill": {
            "Bayview": 19, "Union Square": 7, "Chinatown": 6, "The Castro": 17,
            "Presidio": 17, "Pacific Heights": 8, "Russian Hill": 5
        },
        "Union Square": {
            "Bayview": 15, "Nob Hill": 9, "Chinatown": 7, "The Castro": 19,
            "Presidio": 24, "Pacific Heights": 15, "Russian Hill": 13
        },
        "Chinatown": {
            "Bayview": 22, "Nob Hill": 8, "Union Square": 7, "The Castro": 22,
            "Presidio": 19, "Pacific Heights": 10, "Russian Hill": 7
        },
        "The Castro": {
            "Bayview": 19, "Nob Hill": 16, "Union Square": 19, "Chinatown": 20,
            "Presidio": 20, "Pacific Heights": 16, "Russian Hill": 18
        },
        "Presidio": {
            "Bayview": 31, "Nob Hill": 18, "Union Square": 22, "Chinatown": 21,
            "The Castro": 21, "Pacific Heights": 11, "Russian Hill": 14
        },
        "Pacific Heights": {
            "Bayview": 22, "Nob Hill": 8, "Union Square": 12, "Chinatown": 11,
            "The Castro": 16, "Presidio": 11, "Russian Hill": 7
        },
        "Russian Hill": {
            "Bayview": 23, "Nob Hill": 5, "Union Square": 11, "Chinatown": 9,
            "The Castro": 21, "Presidio": 14, "Pacific Heights": 7
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