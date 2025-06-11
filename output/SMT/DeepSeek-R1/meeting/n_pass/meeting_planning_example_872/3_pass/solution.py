from z3 import *

def main():
    # Travel time matrix: 10 locations (0:Presidio, 1:Haight-Ashbury, 2:Nob Hill, 3:Russian Hill, 4:North Beach, 
    # 5:Chinatown, 6:Union Square, 7:Embarcadero, 8:Financial District, 9:Marina District)
    travel_time = [
        [0, 15, 18, 14, 18, 21, 22, 20, 23, 11],
        [15, 0, 15, 17, 19, 19, 19, 20, 21, 17],
        [17, 13, 0, 5, 8, 6, 7, 9, 9, 11],
        [14, 17, 5, 0, 5, 9, 10, 8, 11, 7],
        [17, 18, 7, 4, 0, 6, 7, 6, 8, 9],
        [19, 19, 9, 7, 3, 0, 7, 5, 5, 12],
        [24, 18, 9, 13, 10, 7, 0, 11, 9, 18],
        [20, 21, 10, 8, 5, 7, 10, 0, 5, 12],
        [22, 19, 8, 11, 7, 5, 9, 4, 0, 15],
        [10, 16, 12, 8, 11, 15, 16, 14, 17, 0]
    ]
    
    # Friend locations: indices 1 to 9 correspond to friends
    # Available start and end times in minutes from 9:00 AM
    available_start = {
        1: 720,   # Karen (Haight-Ashbury): 9:00 PM to 9:45 PM
        2: 285,   # Jessica (Nob Hill): 1:45 PM to 9:00 PM
        3: 390,   # Brian (Russian Hill): 3:30 PM to 9:45 PM
        4: 45,    # Kenneth (North Beach): 9:45 AM to 9:00 PM
        5: -45,   # Jason (Chinatown): 8:15 AM to 11:45 AM
        6: 345,   # Stephanie (Union Square): 2:45 PM to 6:45 PM
        7: 45,    # Kimberly (Embarcadero): 9:45 AM to 7:30 PM
        8: -105,  # Steven (Financial District): 7:15 AM to 9:15 PM
        9: 75     # Mark (Marina District): 10:15 AM to 1:00 PM
    }
    
    available_end = {
        1: 765,   # Karen: 9:45 PM
        2: 720,   # Jessica: 9:00 PM
        3: 765,   # Brian: 9:45 PM
        4: 720,   # Kenneth: 9:00 PM
        5: 165,   # Jason: 11:45 AM
        6: 585,   # Stephanie: 6:45 PM
        7: 630,   # Kimberly: 7:30 PM
        8: 735,   # Steven: 9:15 PM
        9: 240    # Mark: 1:00 PM
    }
    
    durations = {
        1: 45,    # Karen
        2: 90,    # Jessica
        3: 60,    # Brian
        4: 30,    # Kenneth
        5: 75,    # Jason
        6: 105,   # Stephanie
        7: 75,    # Kimberly
        8: 60,    # Steven
        9: 75     # Mark
    }
    
    friend_names = {
        1: "Karen",
        2: "Jessica",
        3: "Brian",
        4: "Kenneth",
        5: "Jason",
        6: "Stephanie",
        7: "Kimberly",
        8: "Steven",
        9: "Mark"
    }
    
    # Create solver
    s = Solver()
    
    # Variables
    x = {}
    for i in range(0, 10):
        for j in range(1, 10):
            if i != j:
                x[(i, j)] = Bool(f"x_{i}_{j}")
    
    u = {}
    for j in range(1, 10):
        u[j] = Int(f"u_{j}")
        s.add(Or(u[j] == 0, And(u[j] >= 1, u[j] <= 9)))
    
    start = {}
    for j in range(1, 10):
        start[j] = Real(f"start_{j}")
    
    # Total met friends
    total_met = Sum([If(u[j] >= 1, 1, 0) for j in range(1, 10)])
    
    # Constraints
    for j in range(1, 10):
        incoming = []
        for i in range(0, 10):
            if i != j:
                incoming.append(x.get((i, j), BoolVal(False)))
        s.add(Sum([If(inc, 1, 0) for inc in incoming]) == If(u[j] >= 1, 1, 0))
        
        s.add(Implies(u[j] >= 1, start[j] >= available_start[j]))
        s.add(Implies(u[j] >= 1, start[j] + durations[j] <= available_end[j]))
    
    outgoing0 = [x.get((0, j), BoolVal(False)) for j in range(1, 10)]
    s.add(Sum([If(edge, 1, 0) for edge in outgoing0]) == If(total_met > 0, 1, 0))
    
    for j in range(1, 10):
        s.add(Implies(x[(0, j)], u[j] == 1))
    
    for i in range(1, 10):
        for j in range(1, 10):
            if i != j:
                edge = x.get((i, j))
                if edge is not None:
                    s.add(Implies(edge, u[j] == u[i] + 1))
    
    for i in range(0, 10):
        for j in range(1, 10):
            if i != j:
                edge = x.get((i, j))
                if edge is not None:
                    if i == 0:
                        s.add(Implies(edge, start[j] >= travel_time[i][j]))
                    else:
                        s.add(Implies(edge, start[j] >= start[i] + durations[i] + travel_time[i][j]))
    
    # Ensure distinct positions for met friends
    for j in range(1, 10):
        for k in range(j+1, 10):
            s.add(Implies(And(u[j] >= 1, u[k] >= 1), u[j] != u[k]))
    
    # Solve with iterative maximization
    found = False
    max_met = 0
    model = None
    for n in range(9, 0, -1):
        s.push()
        s.add(total_met == n)
        if s.check() == sat:
            m = s.model()
            max_met = n
            model = m
            found = True
            break
        else:
            s.pop()
    
    if not found:
        print("SOLUTION: No feasible schedule found.")
        return
    
    print(f"SOLUTION: Met {max_met} friends")
    schedule = []
    for j in range(1, 10):
        u_val = model[u[j]]
        if isinstance(u_val, IntNumRef) and u_val.as_long() >= 1:
            start_val = model[start[j]]
            if is_rational_value(start_val):
                start_minutes = start_val.numerator_as_long() / start_val.denominator_as_long()
                total_minutes = int(round(start_minutes))
                hours = total_minutes // 60
                minutes = total_minutes % 60
                start_time = f"{9 + hours}:{minutes:02d}"
                end_minutes = total_minutes + durations[j]
                end_hours = end_minutes // 60
                end_minutes = end_minutes % 60
                end_time = f"{9 + end_hours}:{end_minutes:02d}"
                schedule.append((u_val.as_long(), j, start_time, end_time))
    
    schedule.sort()
    for pos, j, start_str, end_str in schedule:
        print(f"Meet {friend_names[j]} from {start_str} to {end_str} (Position {pos})")

if __name__ == "__main__":
    main()