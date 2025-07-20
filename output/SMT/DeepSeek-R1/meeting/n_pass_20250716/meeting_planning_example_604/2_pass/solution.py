from z3 import *

def main():
    travel_time = [
        [0, 26, 25, 7, 20, 6],
        [24, 0, 11, 18, 8, 20],
        [24, 13, 0, 19, 10, 24],
        [7, 21, 21, 0, 15, 5],
        [19, 8, 9, 13, 0, 16],
        [5, 22, 22, 4, 16, 0]
    ]
    
    friends = [
        ("Laura", 1, 105, 645, 750),
        ("Daniel", 2, 15, 735, 765),
        ("Karen", 3, 30, 330, 645),
        ("Joseph", 4, 15, 150, 225),
        ("Kimberly", 5, 30, 405, 615)
    ]
    n_friends = len(friends)
    
    s = Optimize()
    
    meet = [Bool(f'meet_{i}') for i in range(n_friends)]
    start = [Int(f'start_{i}') for i in range(n_friends)]
    order = [Int(f'order_{i}') for i in range(n_friends)]
    
    for i in range(n_friends):
        s.add(If(meet[i], And(order[i] >= 0, order[i] < n_friends), order[i] == -1))
    
    for i in range(n_friends):
        for j in range(i + 1, n_friends):
            s.add(Implies(And(meet[i], meet[j]), order[i] != order[j]))
    
    for i in range(n_friends):
        name, loc_i, dur_i, avail_s_i, avail_e_i = friends[i]
        s.add(Implies(meet[i], start[i] >= avail_s_i))
        s.add(Implies(meet[i], start[i] <= avail_e_i - dur_i))
        
        s.add(Implies(And(meet[i], order[i] == 0), start[i] >= travel_time[0][loc_i]))
        
        for j in range(n_friends):
            if i == j:
                continue
            name_j, loc_j, dur_j, _, _ = friends[j]
            s.add(Implies(
                And(meet[i], meet[j], order[j] == order[i] - 1),
                start[i] >= start[j] + dur_j + travel_time[loc_j][loc_i]
            ))
    
    s.maximize(Sum([If(meet[i], 1, 0) for i in range(n_friends)]))
    
    if s.check() == sat:
        m = s.model()
        total_met = 0
        schedule = []
        for i in range(n_friends):
            if m.eval(meet[i]):
                total_met += 1
                start_val = m.eval(start[i]).as_long()
                hours = 9 + start_val // 60
                minutes = start_val % 60
                start_str = f"{hours}:{minutes:02d}"
                schedule.append((friends[i][0], start_str, start_val))
        print(f"Total friends met: {total_met}")
        schedule.sort(key=lambda x: x[2])
        for name, start_str, _ in schedule:
            print(f"Meet {name} at {start_str}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()