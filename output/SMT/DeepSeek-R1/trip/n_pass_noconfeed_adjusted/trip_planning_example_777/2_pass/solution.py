from z3 import *
import json

def main():
    cities = ['Dublin', 'Helsinki', 'Riga', 'Reykjavik', 'Vienna', 'Tallinn']
    required_days = [5, 3, 3, 2, 2, 5]
    fixed_s = [None, 3, None, None, 2, 7]
    fixed_e = [None, 5, None, None, 3, 11]
    
    allowed_edges_set = {(0,1), (0,2), (0,3), (0,4), (0,5), (1,2), (1,3), (1,4), (1,5), (2,4), (2,5), (3,4)}
    
    solver = Solver()
    
    s_vars = [Int(f's_{i}') for i in range(6)]
    e_vars = [Int(f'e_{i}') for i in range(6)]
    order = [Int(f'order_{i}') for i in range(6)]
    
    for i in range(6):
        solver.add(And(0 <= order[i], order[i] <= 5))
    solver.add(Distinct(order))
    
    for i in range(6):
        solver.add(e_vars[i] - s_vars[i] + 1 == required_days[i])
        solver.add(s_vars[i] <= e_vars[i])
        if fixed_s[i] is not None:
            solver.add(s_vars[i] == fixed_s[i])
        if fixed_e[i] is not None:
            solver.add(e_vars[i] == fixed_e[i])
    
    # First city starts at day 1
    solver.add(And([If(order[0] == i, s_vars[i] == 1, True) for i in range(6)]))
    # Last city ends at day 15
    solver.add(And([If(order[5] == i, e_vars[i] == 15, True) for i in range(6)]))
    
    # Consecutive cities must have end day of previous equal to start day of next
    for idx in range(5):
        for i in range(6):
            for j in range(6):
                solver.add(If(And(order[idx] == i, order[idx+1] == j), e_vars[i] == s_vars[j], True))
    
    # Allowed edges constraint
    for idx in range(5):
        edge_constraints = []
        for edge in allowed_edges_set:
            a, b = edge
            edge_constraints.append(And(order[idx] == a, order[idx+1] == b))
            edge_constraints.append(And(order[idx] == b, order[idx+1] == a))
        solver.add(Or(edge_constraints))
    
    if solver.check() == sat:
        model = solver.model()
        order_val = [model.evaluate(order[i]).as_long() for i in range(6)]
        s_val = [model.evaluate(s_vars[i]).as_long() for i in range(6)]
        e_val = [model.evaluate(e_vars[i]).as_long() for i in range(6)]
        
        itinerary = []
        for city_index in order_val:
            start = s_val[city_index]
            end = e_val[city_index]
            place = cities[city_index]
            if start == end:
                day_range_str = f"Day {start}"
            else:
                day_range_str = f"Day {start}-{end}"
            itinerary.append({"day_range": day_range_str, "place": place})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()