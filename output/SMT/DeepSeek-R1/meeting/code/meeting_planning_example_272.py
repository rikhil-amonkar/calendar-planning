from z3 import *

def main():
    # Friends data: name, location, start (min), end (min), duration (min)
    friends = [
        ("Patricia", "Nob Hill", 18*60+30, 21*60+45, 90),
        ("Ashley", "Mission District", 20*60+30, 21*60+15, 45),
        ("Timothy", "Embarcadero", 9*60+45, 17*60+45, 120)
    ]
    
    # Travel times matrix
    travel = {
        "Russian Hill": {
            "Nob Hill": 5,
            "Mission District": 16,
            "Embarcadero": 8
        },
        "Nob Hill": {
            "Russian Hill": 5,
            "Mission District": 13,
            "Embarcadero": 9
        },
        "Mission District": {
            "Russian Hill": 15,
            "Nob Hill": 12,
            "Embarcadero": 19
        },
        "Embarcadero": {
            "Russian Hill": 8,
            "Nob Hill": 10,
            "Mission District": 20
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
    
    # Arrival from Russian Hill (starting point at 9:00 AM = 540 min)
    for name, loc, _, _, _, v, a, d in friend_vars:
        s.add(Implies(v, a >= 540 + travel["Russian Hill"][loc]))
    
    # Maximize number of friends visited
    total = Sum([If(v, 1, 0) for (_,_,_,_,_, v,_,_) in friend_vars])
    s.maximize(total)
    
    if s.check() == sat:
        m = s.model()
        print("Optimal schedule:")
        for name, _, _, _, _, v, a, d in friend_vars:
            if m.eval(v):
                a_val = m.eval(a).as_long()
                d_val = m.eval(d).as_long()
                print(f"{name}: {a_val//60:02}:{a_val%60:02} - {d_val//60:02}:{d_val%60:02}")
    else:
        print("No valid schedule found.")

if __name__ == "__main__":
    main()