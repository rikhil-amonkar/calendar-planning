from z3 import *

def main():
    cities = ['Reykjavik', 'Munich', 'Stockholm', 'Barcelona', 'Bucharest', 'Split']
    durations_dict = {
        'Reykjavik': 5,
        'Munich': 4,
        'Stockholm': 4,
        'Barcelona': 3,
        'Bucharest': 2,
        'Split': 3
    }
    
    graph = {
        'Reykjavik': ['Munich', 'Oslo', 'Frankfurt', 'Barcelona', 'Stockholm'],
        'Munich': ['Reykjavik', 'Frankfurt', 'Bucharest', 'Oslo', 'Barcelona', 'Split', 'Stockholm'],
        'Frankfurt': ['Munich', 'Oslo', 'Barcelona', 'Reykjavik', 'Bucharest', 'Split', 'Stockholm'],
        'Oslo': ['Split', 'Reykjavik', 'Bucharest', 'Frankfurt', 'Barcelona', 'Stockholm', 'Munich'],
        'Bucharest': ['Munich', 'Barcelona', 'Oslo', 'Frankfurt'],
        'Barcelona': ['Bucharest', 'Frankfurt', 'Reykjavik', 'Stockholm', 'Split', 'Oslo', 'Munich'],
        'Stockholm': ['Barcelona', 'Reykjavik', 'Split', 'Oslo', 'Munich', 'Frankfurt'],
        'Split': ['Oslo', 'Barcelona', 'Stockholm', 'Frankfurt', 'Munich']
    }
    
    conn_matrix = [[False]*6 for _ in range(6)]
    for i in range(6):
        for j in range(6):
            if i == j:
                continue
            c1 = cities[i]
            c2 = cities[j]
            if c2 in graph[c1]:
                conn_matrix[i][j] = True
    
    idx = [Int('idx_%d' % i) for i in range(6)]
    s = Solver()
    
    for i in range(6):
        s.add(idx[i] >= 0, idx[i] < 6)
    s.add(Distinct(idx))
    
    dur = [Int('dur_%d' % i) for i in range(6)]
    for i in range(6):
        s.add(dur[i] == If(idx[i] == 0, durations_dict[cities[0]],
                          If(idx[i] == 1, durations_dict[cities[1]],
                          If(idx[i] == 2, durations_dict[cities[2]],
                          If(idx[i] == 3, durations_dict[cities[3]],
                          If(idx[i] == 4, durations_dict[cities[4]],
                          durations_dict[cities[5]])))))
    
    cum_sum0 = 0
    cum_sum1 = cum_sum0 + dur[0]
    cum_sum2 = cum_sum1 + dur[1]
    cum_sum3 = cum_sum2 + dur[2]
    cum_sum4 = cum_sum3 + dur[3]
    cum_sum5 = cum_sum4 + dur[4]
    cum_sum6 = cum_sum5 + dur[5]
    
    reyk_constraint = Or(
        And(idx[0] == 0, 1 + cum_sum0 - 0 <= 13, 1 + cum_sum1 - 1 >= 9),
        And(idx[1] == 0, 1 + cum_sum1 - 1 <= 13, 1 + cum_sum2 - 2 >= 9),
        And(idx[2] == 0, 1 + cum_sum2 - 2 <= 13, 1 + cum_sum3 - 3 >= 9),
        And(idx[3] == 0, 1 + cum_sum3 - 3 <= 13, 1 + cum_sum4 - 4 >= 9),
        And(idx[4] == 0, 1 + cum_sum4 - 4 <= 13, 1 + cum_sum5 - 5 >= 9),
        And(idx[5] == 0, 1 + cum_sum5 - 5 <= 13, 1 + cum_sum6 - 6 >= 9)
    )
    
    munich_constraint = Or(
        And(idx[0] == 1, 1 + cum_sum1 - 1 >= 13),
        And(idx[1] == 1, 1 + cum_sum2 - 2 >= 13),
        And(idx[2] == 1, 1 + cum_sum3 - 3 >= 13),
        And(idx[3] == 1, 1 + cum_sum4 - 4 >= 13),
        And(idx[4] == 1, 1 + cum_sum5 - 5 >= 13),
        And(idx[5] == 1, 1 + cum_sum6 - 6 >= 13)
    )
    
    s.add(reyk_constraint)
    s.add(munich_constraint)
    
    for i in range(5):
        constraints = []
        for k in range(6):
            for l in range(6):
                if conn_matrix[k][l]:
                    constraints.append(And(idx[i] == k, idx[i+1] == l))
        s.add(Or(constraints))
    
    if s.check() == sat:
        model = s.model()
        idx_vals = []
        for i in range(6):
            val = model[idx[i]]
            idx_vals.append(val.as_long())
        
        first6 = [cities[i] for i in idx_vals]
        dur_vals = [durations_dict[city] for city in first6]
        
        sequence = first6 + ['Oslo', 'Frankfurt']
        starts = [0] * 8
        ends = [0] * 8
        
        starts[0] = 1
        ends[0] = starts[0] + dur_vals[0] - 1
        for i in range(1, 6):
            starts[i] = ends[i-1]
            ends[i] = starts[i] + dur_vals[i] - 1
        starts[6] = 16
        ends[6] = 17
        starts[7] = 17
        ends[7] = 20
        
        itinerary = []
        for i in range(8):
            s_val = starts[i]
            e_val = ends[i]
            if s_val == e_val:
                day_range_str = "Day %d" % s_val
            else:
                day_range_str = "Day %d-%d" % (s_val, e_val)
            itinerary.append({"day_range": day_range_str, "place": sequence[i]})
            
            if i < 7:
                day_str = "Day %d" % e_val
                itinerary.append({"day_range": day_str, "place": sequence[i]})
                itinerary.append({"day_range": day_str, "place": sequence[i+1]})
        
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == '__main__':
    main()