from z3 import *

def main():
    # Friends data: name, location, start (min), end (min), duration (min)
    friends = [
        ("Virtual", "Presidio", 9*60, 9*60, 0),
        ("Karen", "Haight-Ashbury", 21*60, 21*60+45, 45),
        ("Jessica", "Nob Hill", 13*60+45, 21*60, 90),
        ("Brian", "Russian Hill", 15*60+30, 21*60+45, 60),
        ("Kenneth", "North Beach", 9*60+45, 21*60, 30),
        ("Jason", "Chinatown", 8*60+15, 11*60+45, 75),
        ("Stephanie", "Union Square", 14*60+45, 18*60+45, 105),
        ("Kimberly", "Embarcadero", 9*60+45, 19*60+30, 75),
        ("Steven", "Financial District", 7*60+15, 21*60+15, 60),
        ("Mark", "Marina District", 10*60+15, 13*60, 75)
    ]
    
    # Travel times matrix
    travel = {
        "Presidio": {
            "Haight-Ashbury": 15, "Nob Hill": 18, "Russian Hill": 14, "North Beach": 18,
            "Chinatown": 21, "Union Square": 22, "Embarcadero": 20, "Financial District": 23,
            "Marina District": 11
        },
        "Haight-Ashbury": {
            "Presidio": 15, "Nob Hill": 15, "Russian Hill": 17, "North Beach": 19,
            "Chinatown": 19, "Union Square": 19, "Embarcadero": 20, "Financial District": 21,
            "Marina District": 17
        },
        "Nob Hill": {
            "Presidio": 17, "Haight-Ashbury": 13, "Russian Hill": 5, "North Beach": 8,
            "Chinatown": 6, "Union Square": 7, "Embarcadero": 9, "Financial District": 9,
            "Marina District": 11
        },
        "Russian Hill": {
            "Presidio": 14, "Haight-Ashbury": 17, "Nob Hill": 5, "North Beach": 5,
            "Chinatown": 9, "Union Square": 10, "Embarcadero": 8, "Financial District": 11,
            "Marina District": 7
        },
        "North Beach": {
            "Presidio": 17, "Haight-Ashbury": 18, "Nob Hill": 7, "Russian Hill": 4,
            "Chinatown": 6, "Union Square": 7, "Embarcadero": 6, "Financial District": 8,
            "Marina District": 9
        },
        "Chinatown": {
            "Presidio": 19, "Haight-Ashbury": 19, "Nob Hill": 9, "Russian Hill": 7,
            "North Beach": 3, "Union Square": 7, "Embarcadero": 5, "Financial District": 5,
            "Marina District": 12
        },
        "Union Square": {
            "Presidio": 24, "Haight-Ashbury": 18, "Nob Hill": 9, "Russian Hill": 13,
            "North Beach": 10, "Chinatown": 7, "Embarcadero": 11, "Financial District": 9,
            "Marina District": 18
        },
        "Embarcadero": {
            "Presidio": 20, "Haight-Ashbury": 21, "Nob Hill": 10, "Russian Hill": 8,
            "North Beach": 5, "Chinatown": 7, "Union Square": 10, "Financial District": 5,
            "Marina District": 12
        },
        "Financial District": {
            "Presidio": 22, "Haight-Ashbury": 19, "Nob Hill": 8, "Russian Hill": 11,
            "North Beach": 7, "Chinatown": 5, "Union Square": 9, "Embarcadero": 4,
            "Marina District": 15
        },
        "Marina District": {
            "Presidio": 10, "Haight-Ashbury": 16, "Nob Hill": 12, "Russian Hill": 8,
            "North Beach": 11, "Chinatown": 15, "Union Square": 16, "Embarcadero": 14,
            "Financial District": 17
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