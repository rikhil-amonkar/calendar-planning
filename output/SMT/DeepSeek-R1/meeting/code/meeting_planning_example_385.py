from z3 import *

def main():
    # Friends data: name, location, start (min), end (min), duration (min)
    friends = [
        ("Virtual", "Nob Hill", 9*60, 9*60, 0),
        ("Jeffrey", "Presidio", 8*60, 10*60, 105),
        ("Steven", "North Beach", 13*60+30, 22*60, 45),
        ("Barbara", "Fisherman's Wharf", 18*60, 21*60+30, 30),
        ("John", "Pacific Heights", 9*60, 13*60+30, 15)
    ]
    
    # Travel times matrix
    travel = {
        "Nob Hill": {
            "Presidio": 17, "North Beach": 8, "Fisherman's Wharf": 11, "Pacific Heights": 8
        },
        "Presidio": {
            "Nob Hill": 18, "North Beach": 18, "Fisherman's Wharf": 19, "Pacific Heights": 11
        },
        "North Beach": {
            "Nob Hill": 7, "Presidio": 17, "Fisherman's Wharf": 5, "Pacific Heights": 8
        },
        "Fisherman's Wharf": {
            "Nob Hill": 11, "Presidio": 17, "North Beach": 6, "Pacific Heights": 12
        },
        "Pacific Heights": {
            "Nob Hill": 8, "Presidio": 11, "North Beach": 9, "Fisherman's Wharf": 13
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
                if loc_i in travel and loc_j in travel[loc_i]:
                    travel_time = travel[loc_i][loc_j]
                    s.add(Implies(And(b, vi, vj), aj >= di + travel_time))
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