from z3 import *

def main():
    s = Optimize()
    
    n = 6  # 0: dummy, 1: Thomas, 2: Stephanie, 3: Laura, 4: Betty, 5: Patricia
    meet = [Bool(f'meet_{i}') for i in range(n)]
    start = [Int(f'start_{i}') for i in range(n)]
    
    s.add(meet[0] == True)
    s.add(start[0] == 0)
    
    dur = [0, 120, 30, 30, 45, 45]
    
    loc_index = [0, 1, 2, 3, 4, 5]
    loc_names = ["Fisherman's Wharf", "Bayview", "Golden Gate Park", "Nob Hill", "Marina District", "Embarcadero"]
    friend_names = ["Dummy", "Thomas", "Stephanie", "Laura", "Betty", "Patricia"]
    
    avail_start = [0, 390, 570, 0, 585, 510]
    avail_end = [0, 570, 765, 435, 765, 780]
    
    travel = [
        [0, 26, 25, 11, 9, 8],
        [25, 0, 22, 20, 25, 19],
        [24, 23, 0, 20, 16, 25],
        [11, 19, 17, 0, 11, 9],
        [10, 27, 18, 12, 0, 14],
        [6, 21, 25, 10, 12, 0]
    ]
    
    for i in range(1, n):
        s.add(If(meet[i], start[i] >= avail_start[i], True))
        s.add(If(meet[i], start[i] + dur[i] <= avail_end[i], True))
        s.add(If(meet[i], start[i] >= travel[0][loc_index[i]], True))
    
    for i in range(n):
        for j in range(n):
            if i != j and i >= 1 and j >= 1:
                s.add(If(And(meet[i], meet[j]), 
                          Or(start[i] >= start[j] + dur[j] + travel[loc_index[j]][loc_index[i]], 
                             start[j] >= start[i] + dur[i] + travel[loc_index[i]][loc_index[j]]), 
                          True))
            if i != j and i == 0 and j >= 1:
                s.add(If(meet[j], start[j] >= start[0] + dur[0] + travel[loc_index[0]][loc_index[j]], True))
            if i != j and j == 0 and i >= 1:
                s.add(If(meet[i], start[i] >= start[0] + dur[0] + travel[loc_index[0]][loc_index[i]], True))
    
    total_meet = Sum([If(meet[i], 1, 0) for i in range(1, n)])
    s.maximize(total_meet)
    
    if s.check() == sat:
        m = s.model()
        total_friends = m.evaluate(total_meet)
        print(f"Total friends met: {total_friends}")
        print("Schedule:")
        for i in range(n):
            if i == 0 or m[meet[i]]:
                stime = m[start[i]]
                if is_int_value(stime):
                    mins = stime.as_long()
                    hours = 9 + mins // 60
                    mins = mins % 60
                    time_str = f"{hours}:{mins:02d}"
                else:
                    time_str = str(stime)
                if i == 0:
                    print(f"  - Dummy meeting at {loc_names[loc_index[i]]} (Start: {time_str}, Duration: {dur[i]} min)")
                else:
                    print(f"  - Meet {friend_names[i]} at {loc_names[loc_index[i]]} (Start: {time_str}, Duration: {dur[i]} min)")
    else:
        print("No solution found.")

def is_int_value(v):
    return isinstance(v, IntNumRef)

if __name__ == "__main__":
    main()