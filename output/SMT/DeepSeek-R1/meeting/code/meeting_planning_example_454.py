from z3 import *

def main():
    # Friends data: name, location, start (min), end (min), duration (min)
    friends = [
        ("Jessica", "Golden Gate Park", 13*60+45, 15*60, 30),
        ("Ashley", "Bayview", 17*60+15, 20*60, 105),
        ("Ronald", "Chinatown", 7*60+15, 14*60+45, 90),
        ("William", "North Beach", 13*60+15, 20*60+15, 15),
        ("Daniel", "Mission District", 7*60, 11*60+15, 105)
    ]
    
    # Travel times matrix
    travel = {
        "Presidio": {
            "Golden Gate Park": 12, "Bayview": 31, "Chinatown": 21,
            "North Beach": 18, "Mission District": 26
        },
        "Golden Gate Park": {
            "Presidio": 11, "Bayview": 23, "Chinatown": 23,
            "North Beach": 24, "Mission District": 17
        },
        "Bayview": {
            "Presidio": 31, "Golden Gate Park": 22, "Chinatown": 18,
            "North Beach": 21, "Mission District": 13
        },
        "Chinatown": {
            "Presidio": 19, "Golden Gate Park": 23, "Bayview": 22,
            "North Beach": 3, "Mission District": 18
        },
        "North Beach": {
            "Presidio": 17, "Golden Gate Park": 22, "Bayview": 22,
            "Chinatown": 6, "Mission District": 18
        },
        "Mission District": {
            "Presidio": 25, "Golden Gate Park": 17, "Bayview": 15,
            "Chinatown": 16, "North Beach": 17
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
    
    # Presidio departure time
    presidio_depart = 540  # 9:00 AM
    
    # Friends must be within their time windows and have sufficient duration if visited
    for name, loc, start, end, dur, visited, a, d in friend_vars:
        s.add(Implies(visited, And(a >= start, d <= end, d >= a + dur)))
    
    # Ordering and travel time constraints
    B = {}
    for i, (name_i, loc_i, _, _, _, vi, ai, di) in enumerate(friend_vars):
        for j, (name_j, loc_j, _, _, _, vj, aj, dj) in enumerate(friend_vars):
            if i != j:
                b = Bool(f'b_{name_i}_{name_j}')
                B[(i,j)] = b
                # If both visited, one must come before the other
                s.add(Implies(And(vi, vj), Or(b, B[(j,i)])))
                s.add(Implies(And(b, vi, vj), aj >= di + travel[loc_i][loc_j]))
                s.add(Implies(b, Not(B[(j,i)])))
    
    # Arrival from Presidio if first friend
    for name, loc, _, _, _, visited, a, d in friend_vars:
        s.add(Implies(visited, a >= presidio_depart + travel["Presidio"][loc]))
    
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