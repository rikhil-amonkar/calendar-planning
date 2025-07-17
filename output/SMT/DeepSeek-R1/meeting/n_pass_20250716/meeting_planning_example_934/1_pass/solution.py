from z3 import *

def main():
    # Friend indices and data
    n = 10
    names = ["Mary", "Kenneth", "Joseph", "Sarah", "Thomas", "Daniel", "Richard", "Mark", "David", "Karen"]
    locations = ["Embarcadero", "The Castro", "Haight-Ashbury", "Union Square", "North Beach", 
                 "Pacific Heights", "Chinatown", "Golden Gate Park", "Marina District", "Russian Hill"]
    
    # Travel times from Nob Hill to each friend
    travel_nob_hill = [9, 17, 13, 7, 8, 8, 6, 17, 11, 5]
    
    # Travel time matrix between friends (10x10)
    travel_matrix = [
        [0, 25, 21, 10, 5, 11, 7, 25, 12, 8],
        [22, 0, 6, 19, 20, 16, 22, 11, 21, 18],
        [20, 6, 0, 19, 19, 12, 19, 7, 17, 17],
        [11, 17, 18, 0, 10, 15, 7, 22, 18, 13],
        [6, 23, 18, 7, 0, 8, 6, 22, 9, 4],
        [10, 16, 11, 12, 9, 0, 11, 15, 6, 7],
        [5, 22, 19, 7, 3, 10, 0, 23, 12, 7],
        [25, 13, 7, 22, 23, 16, 23, 0, 16, 19],
        [14, 22, 16, 16, 11, 7, 15, 18, 0, 8],
        [8, 21, 17, 10, 5, 7, 9, 21, 7, 0]
    ]
    
    # Available times (in minutes from 9:00 AM) and minimum durations
    available_start = [660, 135, 660, 165, 615, 285, 0, 510, 660, 255]
    available_end = [735, 615, 780, 330, 645, 690, 585, 750, 720, 570]
    min_duration = [75, 30, 120, 90, 15, 15, 30, 120, 60, 120]
    
    # Create Z3 variables
    met = [Bool(f'met_{i}') for i in range(n)]
    start = [Int(f'start_{i}') for i in range(n)]
    end = [Int(f'end_{i}') for i in range(n)]
    
    s = Solver()
    
    # Constraint 1: Time windows and durations for met friends
    for i in range(n):
        s.add(Implies(met[i], start[i] >= available_start[i]))
        s.add(Implies(met[i], end[i] <= available_end[i]))
        s.add(Implies(met[i], end[i] - start[i] >= min_duration[i]))
        s.add(Implies(met[i], start[i] >= 0))
        s.add(Implies(met[i], end[i] >= 0))
    
    # Constraint 2: Travel constraints (from Nob Hill or another meeting)
    for i in range(n):
        # Condition: start_i >= travel_nob_hill[i] OR exists j (j != i) such that (met[j] and start_i >= end_j + travel_matrix[j][i])
        nob_hill_cond = (start[i] >= travel_nob_hill[i])
        other_conds = []
        for j in range(n):
            if i == j:
                continue
            cond_j = And(met[j], start[i] >= end[j] + travel_matrix[j][i])
            other_conds.append(cond_j)
        if other_conds:
            s.add(Implies(met[i], Or(nob_hill_cond, Or(other_conds))))
        else:
            s.add(Implies(met[i], nob_hill_cond))
    
    # Constraint 3: Disjunctive scheduling for every pair of friends
    for i in range(n):
        for j in range(i+1, n):
            cond1 = (end[i] + travel_matrix[i][j] <= start[j])
            cond2 = (end[j] + travel_matrix[j][i] <= start[i])
            s.add(Implies(And(met[i], met[j]), Or(cond1, cond2)))
    
    # Maximize the number of friends met
    opt = Optimize()
    opt.add(s.assertions())
    num_met = Sum([If(met[i], 1, 0) for i in range(n)])
    h = opt.maximize(num_met)
    opt.set(timeout=300000)  # 5 minutes timeout
    
    # Check and get the solution
    if opt.check() == sat:
        m = opt.model()
        total_met = m.evaluate(num_met)
        schedule = []
        for i in range(n):
            if m.evaluate(met[i]):
                s_val = m.evaluate(start[i])
                e_val = m.evaluate(end[i])
                if isinstance(s_val, IntNumRef) and isinstance(e_val, IntNumRef):
                    s_min = s_val.as_long()
                    e_min = e_val.as_long()
                    schedule.append((i, s_min, e_min))
        schedule.sort(key=lambda x: x[1])  # Sort by start time
        
        # Format and print the schedule
        print(f"Number of friends met: {total_met}")
        for i, s_min, e_min in schedule:
            # Convert minutes to time (from 9:00 AM)
            start_hr = 9 + s_min // 60
            start_min = s_min % 60
            end_hr = 9 + e_min // 60
            end_min = e_min % 60
            
            # Format to AM/PM
            start_ampm = "AM" if start_hr < 12 else "PM"
            end_ampm = "AM" if end_hr < 12 else "PM"
            start_hr12 = start_hr if start_hr <= 12 else start_hr - 12
            end_hr12 = end_hr if end_hr <= 12 else end_hr - 12
            if start_hr12 == 0: start_hr12 = 12
            if end_hr12 == 0: end_hr12 = 12
            
            start_str = f"{start_hr12}:{start_min:02d} {start_ampm}"
            end_str = f"{end_hr12}:{end_min:02d} {end_ampm}"
            
            print(f"Meet {names[i]} from {start_str} to {end_str} at {locations[i]}")
    else:
        print("No solution found")

if __name__ == '__main__':
    main()