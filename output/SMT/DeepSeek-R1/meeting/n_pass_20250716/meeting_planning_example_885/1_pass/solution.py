from z3 import *

def main():
    # Travel time matrix (10x10: 0=Russian Hill, 1=Marina, 2=Financial, 3=Alamo, 4=Golden Gate, 5=Castro, 6=Bayview, 7=Sunset, 8=Haight, 9=Nob)
    travel_time = [
        [0, 7, 11, 15, 21, 21, 23, 23, 17, 5],
        [8, 0, 17, 15, 18, 22, 27, 19, 16, 12],
        [11, 15, 0, 17, 23, 20, 19, 30, 19, 8],
        [13, 15, 17, 0, 9, 8, 16, 16, 5, 11],
        [19, 16, 26, 9, 0, 13, 23, 10, 7, 20],
        [18, 21, 21, 8, 11, 0, 19, 17, 6, 16],
        [23, 27, 19, 16, 22, 19, 0, 23, 19, 20],
        [24, 21, 30, 17, 11, 17, 22, 0, 15, 27],
        [17, 17, 21, 5, 7, 6, 18, 15, 0, 15],
        [5, 11, 9, 11, 17, 17, 19, 24, 13, 0]
    ]
    
    # Friends data: (index, name, location_index, start_avail, end_avail, min_duration)
    friends = [
        (0, "Mark", 1, 585, 720, 90),
        (1, "Karen", 2, 30, 225, 90),
        (2, "Barbara", 3, 60, 630, 90),
        (3, "Nancy", 4, 465, 660, 105),
        (4, "David", 5, 0, 540, 120),
        (5, "Linda", 6, 555, 645, 45),
        (6, "Kevin", 7, 60, 525, 120),
        (7, "Matthew", 8, 75, 390, 45),
        (8, "Andrew", 9, 165, 465, 105)
    ]
    n_friends = len(friends)
    
    # Extract friend details
    friend_loc = [f[2] for f in friends]
    min_duration = [f[5] for f in friends]
    start_avail = [f[3] for f in friends]
    end_avail = [f[4] for f in friends]
    
    # Create solver and variables
    s = Solver()
    v = [Bool(f'v_{i}') for i in range(n_friends)]
    s_i = [Int(f's_{i}') for i in range(n_friends)]
    u_i = [Int(f'u_{i}') for i in range(n_friends)]
    N = Int('N')
    
    # Constraint: N is the total number of visited friends
    s.add(N == Sum([If(v[i], 1, 0) for i in range(n_friends)]))
    
    # Time window and duration constraints for each friend if visited
    for i in range(n_friends):
        s.add(Implies(v[i], s_i[i] >= start_avail[i]))
        s.add(Implies(v[i], s_i[i] + min_duration[i] <= end_avail[i]))
        s.add(Implies(v[i], And(u_i[i] >= 1, u_i[i] <= N)))
    
    # Distinct u_i for visited friends
    for i in range(n_friends):
        for j in range(i + 1, n_friends):
            s.add(Implies(And(v[i], v[j]), u_i[i] != u_i[j]))
    
    # Predecessor constraint: if u_i >= 2, there exists a j with u_j = u_i - 1
    for i in range(n_friends):
        disj = []
        for j in range(n_friends):
            if i != j:
                disj.append(And(v[j], u_i[j] == u_i[i] - 1))
        s.add(Implies(And(v[i], u_i[i] >= 2), Or(disj) if disj else False))
    
    # First friend constraint: travel from Russian Hill (0)
    for i in range(n_friends):
        s.add(Implies(And(v[i], u_i[i] == 1), s_i[i] >= travel_time[0][friend_loc[i]]))
    
    # Travel constraint between consecutive friends
    for i in range(n_friends):
        for j in range(n_friends):
            if i != j:
                s.add(Implies(And(v[i], v[j], u_i[j] == u_i[i] + 1),
                              s_i[j] >= s_i[i] + min_duration[i] + travel_time[friend_loc[i]][friend_loc[j]]))
    
    # Start times must be non-negative
    for i in range(n_friends):
        s.add(Implies(v[i], s_i[i] >= 0))
    
    # Maximize N
    max_friends = 0
    model = None
    # Try from max possible (9) down to 1
    for k in range(9, 0, -1):
        s.push()
        s.add(N == k)
        if s.check() == sat:
            model = s.model()
            max_friends = k
            break
        s.pop()
    
    # Output the solution
    if model is None:
        print("No solution found.")
    else:
        print(f"Maximum number of friends met: {max_friends}")
        schedule = []
        for i in range(n_friends):
            if model.evaluate(v[i]):
                order = model.evaluate(u_i[i]).as_long()
                start_val = model.evaluate(s_i[i]).as_long()
                duration = min_duration[i]
                end_val = start_val + duration
                # Convert start_val and end_val to time strings
                start_hour = 9 + start_val // 60
                start_min = start_val % 60
                start_ampm = "AM" if start_hour < 12 else "PM"
                if start_hour > 12:
                    start_hour -= 12
                end_hour = 9 + end_val // 60
                end_min = end_val % 60
                end_ampm = "AM" if end_hour < 12 else "PM"
                if end_hour > 12:
                    end_hour -= 12
                start_str = f"{start_hour}:{start_min:02d}{start_ampm}"
                end_str = f"{end_hour}:{end_min:02d}{end_ampm}"
                schedule.append((order, friends[i][1], start_str, end_str))
        schedule.sort(key=lambda x: x[0])
        for order, name, start_str, end_str in schedule:
            print(f"Meet {name} from {start_str} to {end_str}")

if __name__ == "__main__":
    main()