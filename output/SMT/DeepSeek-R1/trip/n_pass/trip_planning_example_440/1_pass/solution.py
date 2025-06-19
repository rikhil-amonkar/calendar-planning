from z3 import *

def main():
    # City mapping: 0:Split, 1:Helsinki, 2:Reykjavik, 3:Vilnius, 4:Geneva
    dur_dict = {0:2, 1:2, 2:3, 3:3, 4:6}
    city_names = {0:'Split', 1:'Helsinki', 2:'Reykjavik', 3:'Vilnius', 4:'Geneva'}
    
    # Graph: adjacency list
    graph = {
        0: [1, 3, 4],
        1: [0, 2, 3, 4],
        2: [1],
        3: [0, 1],
        4: [0, 1]
    }
    allowed_pairs = set()
    for u, neighbors in graph.items():
        for v in neighbors:
            allowed_pairs.add((u, v))
    
    # Create Z3 variables for the order
    order = [Int(f'order_{i}') for i in range(5)]
    s = Solver()
    
    # Constraints: each order[i] between 0 and 4 and distinct
    for i in range(5):
        s.add(And(order[i] >= 0, order[i] <= 4))
    s.add(Distinct(order))
    
    # Constraints for consecutive cities being connected
    for i in range(4):
        s.add(Or([And(order[i] == u, order[i+1] == v) for (u, v) in allowed_pairs]))
    
    # Define durations for each position in the order
    d = [If(order[i] == 0, dur_dict[0],
          If(order[i] == 1, dur_dict[1],
          If(order[i] == 2, dur_dict[2],
          If(order[i] == 3, dur_dict[3], dur_dict[4])))) for i in range(5)]
    
    # Precomputed sums for the first j durations
    pre = [0] * 5
    pre[0] = 0
    pre[1] = d[0]
    pre[2] = d[0] + d[1]
    pre[3] = d[0] + d[1] + d[2]
    pre[4] = d[0] + d[1] + d[2] + d[3]
    
    # Start and end days for each city in the order
    start_days = [pre[j] - j + 1 for j in range(5)]
    end_days = [pre[j] + d[j] - j for j in range(5)]
    
    # Find positions of Reykjavik (2) and Vilnius (3)
    reykjavik_pos = -1
    vilnius_pos = -1
    for j in range(5):
        reykjavik_pos = If(order[j] == 2, j, reykjavik_pos)
        vilnius_pos = If(order[j] == 3, j, vilnius_pos)
    
    # Constraints for Reykjavik and Vilnius
    reyk_start = If(reykjavik_pos == 0, start_days[0],
                   If(reykjavik_pos == 1, start_days[1],
                   If(reykjavik_pos == 2, start_days[2],
                   If(reykjavik_pos == 3, start_days[3], start_days[4]))))
    reyk_end = If(reykjavik_pos == 0, end_days[0],
                 If(reykjavik_pos == 1, end_days[1],
                 If(reykjavik_pos == 2, end_days[2],
                 If(reykjavik_pos == 3, end_days[3], end_days[4]))))
    s.add(reyk_start <= 12, reyk_end >= 10)
    
    vilnius_start = If(vilnius_pos == 0, start_days[0],
                      If(vilnius_pos == 1, start_days[1],
                      If(vilnius_pos == 2, start_days[2],
                      If(vilnius_pos == 3, start_days[3], start_days[4]))))
    vilnius_end = If(vilnius_pos == 0, end_days[0],
                    If(vilnius_pos == 1, end_days[1],
                    If(vilnius_pos == 2, end_days[2],
                    If(vilnius_pos == 3, end_days[3], end_days[4]))))
    s.add(vilnius_start <= 9, vilnius_end >= 7)
    
    # Check and get model
    if s.check() == sat:
        model = s.model()
        order_val = [model.evaluate(order[i]).as_long() for i in range(5)]
        d_val = [dur_dict[city] for city in order_val]
        pre_val = [0] * 5
        pre_val[0] = 0
        for j in range(1, 5):
            pre_val[j] = pre_val[j-1] + d_val[j-1]
        start_val = [pre_val[j] - j + 1 for j in range(5)]
        end_val = [pre_val[j] + d_val[j] - j for j in range(5)]
        
        itinerary = []
        for j in range(5):
            city = order_val[j]
            start = start_val[j]
            end = end_val[j]
            if j > 0:
                itinerary.append({"day_range": f"Day {start}", "place": city_names[city]})
            if start < end:
                itinerary.append({"day_range": f"Day {start}-{end}", "place": city_names[city]})
            if j < 4:
                itinerary.append({"day_range": f"Day {end}", "place": city_names[city]})
        
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()