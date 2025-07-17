from z3 import *

def main():
    travel_matrix = [
        [0, 17, 8, 11, 8],
        [18, 0, 18, 19, 11],
        [7, 17, 0, 5, 8],
        [11, 17, 6, 0, 12],
        [8, 11, 9, 13, 0]
    ]
    
    friends = [
        {'name': 'Jeffrey', 'loc': 1, 'start': 480, 'end': 600, 'min_dur': 105},
        {'name': 'Steven', 'loc': 2, 'start': 810, 'end': 1320, 'min_dur': 45},
        {'name': 'Barbara', 'loc': 3, 'start': 1080, 'end': 1290, 'min_dur': 30},
        {'name': 'John', 'loc': 4, 'start': 540, 'end': 810, 'min_dur': 15}
    ]
    
    n = len(friends)
    meet = [Bool('meet_%d' % i) for i in range(n)]
    start = [Int('start_%d' % i) for i in range(n)]
    end = [Int('end_%d' % i) for i in range(n)]
    
    before = [[None] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            if i != j:
                before[i][j] = Bool('before_%d_%d' % (i, j))
                
    first = [Bool('first_%d' % i) for i in range(n)]
    
    s = Solver()
    
    for i in range(n):
        s.add(Implies(meet[i], start[i] >= friends[i]['start']))
        s.add(Implies(meet[i], end[i] == start[i] + friends[i]['min_dur']))
        s.add(Implies(meet[i], end[i] <= friends[i]['end']))
        
    for i in range(n):
        for j in range(i + 1, n):
            s.add(Implies(And(meet[i], meet[j]),
                        Or(And(before[i][j], Not(before[j][i])),
                           And(before[j][i], Not(before[i][j])))))
    
    for i in range(n):
        for j in range(n):
            if i != j and before[i][j] is not None:
                loc_i = friends[i]['loc']
                loc_j = friends[j]['loc']
                travel_time = travel_matrix[loc_i][loc_j]
                s.add(Implies(And(meet[i], meet[j], before[i][j]),
                            start[j] >= end[i] + travel_time))
    
    for i in range(n):
        s.add(Implies(first[i], meet[i]))
        other_conds = []
        for j in range(n):
            if i != j:
                other_conds.append(Implies(meet[j], before[i][j]))
        s.add(Implies(first[i], And(other_conds)))
        loc_i = friends[i]['loc']
        travel_time_start = travel_matrix[0][loc_i]
        s.add(Implies(first[i], start[i] >= 540 + travel_time_start))
    
    meet_exists = Or(meet)
    sum_first = Sum([If(first[i], 1, 0) for i in range(n)])
    s.add(If(meet_exists, sum_first == 1, sum_first == 0))
    
    num_met = Sum([If(meet[i], 1, 0) for i in range(n)])
    s.maximize(num_met)
    
    if s.check() == sat:
        m = s.model()
        schedule = []
        for i in range(n):
            if m.evaluate(meet[i]):
                start_val = m.evaluate(start[i]).as_long()
                end_val = m.evaluate(end[i]).as_long()
                schedule.append((friends[i]['name'], start_val, end_val))
        schedule.sort(key=lambda x: x[1])
        print("SOLUTION:")
        for name, start_val, end_val in schedule:
            start_hour = start_val // 60
            start_min = start_val % 60
            end_hour = end_val // 60
            end_min = end_val % 60
            print(f"Meet {name} from {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}")
    else:
        print("No solution found")

if __name__ == '__main__':
    main()