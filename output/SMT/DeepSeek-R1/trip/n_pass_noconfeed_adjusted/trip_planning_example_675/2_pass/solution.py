import z3
import json

def main():
    # City indices
    Dubrovnik = 0
    Split = 1
    Milan = 2
    Porto = 3
    Krakow = 4
    Munich = 5
    
    city_names = ['Dubrovnik', 'Split', 'Milan', 'Porto', 'Krakow', 'Munich']
    days_req = [4, 3, 3, 4, 2, 5]
    
    # Direct flights (undirected)
    allowed_edges = [
        (Munich, Porto), (Porto, Munich),
        (Split, Milan), (Milan, Split),
        (Milan, Porto), (Porto, Milan),
        (Munich, Krakow), (Krakow, Munich),
        (Munich, Milan), (Milan, Munich),
        (Dubrovnik, Munich), (Munich, Dubrovnik),
        (Krakow, Split), (Split, Krakow),
        (Krakow, Milan), (Milan, Krakow),
        (Munich, Split), (Split, Munich)
    ]
    
    solver = z3.Solver()
    
    # Order of cities (permutation)
    order = [z3.Int('order_%i' % i) for i in range(6)]
    for i in range(6):
        solver.add(order[i] >= 0, order[i] <= 5)
    solver.add(z3.Distinct(order))
    
    # End days for each segment
    e0 = z3.Int('e0')
    e1 = z3.Int('e1')
    e2 = z3.Int('e2')
    e3 = z3.Int('e3')
    e4 = z3.Int('e4')
    e5 = z3.Int('e5')
    
    # Helper function to get days required using Z3 expressions
    def get_days(city_idx):
        return z3.If(city_idx == 0, days_req[0],
                z3.If(city_idx == 1, days_req[1],
                z3.If(city_idx == 2, days_req[2],
                z3.If(city_idx == 3, days_req[3],
                z3.If(city_idx == 4, days_req[4], days_req[5])))))
    
    # Constraints for end days using Z3 conditional expressions
    solver.add(e0 == get_days(order[0]))
    solver.add(e1 == e0 + get_days(order[1]) - 1)
    solver.add(e2 == e1 + get_days(order[2]) - 1)
    solver.add(e3 == e2 + get_days(order[3]) - 1)
    solver.add(e4 == e3 + get_days(order[4]) - 1)
    solver.add(e5 == e4 + get_days(order[5]) - 1)
    solver.add(e5 == 16)
    
    # Munich must be at index 2, 3, or 4
    solver.add(z3.Or(order[2] == Munich, order[3] == Munich, order[4] == Munich))
    
    # Start day for a city at index i
    def start_day(i):
        if i == 0:
            return 1
        elif i == 1:
            return e0
        elif i == 2:
            return e1
        elif i == 3:
            return e2
        elif i == 4:
            return e3
        else: # i == 5
            return e4
    
    # Constraints for Milan (must be present between day 11 and 13)
    milan_constraints = []
    for i in range(6):
        milan_constraints.append(z3.And(
            order[i] == Milan,
            start_day(i) <= 13,
            z3.If(i == 0, e0, z3.If(i == 1, e1, z3.If(i == 2, e2, z3.If(i == 3, e3, z3.If(i == 4, e4, e5))))) >= 11
        ))
    solver.add(z3.Or(milan_constraints))
    
    # Constraints for Krakow (must be present between day 8 and 9)
    krakow_constraints = []
    for i in range(6):
        krakow_constraints.append(z3.And(
            order[i] == Krakow,
            start_day(i) <= 9,
            z3.If(i == 0, e0, z3.If(i == 1, e1, z3.If(i == 2, e2, z3.If(i == 3, e3, z3.If(i == 4, e4, e5))))) >= 8
        ))
    solver.add(z3.Or(krakow_constraints))
    
    # Constraints for direct flights between consecutive cities
    for i in range(5):
        edge_constraints = []
        for edge in allowed_edges:
            edge_constraints.append(z3.And(order[i] == edge[0], order[i+1] == edge[1]))
        solver.add(z3.Or(edge_constraints))
    
    # Check and get model
    if solver.check() == z3.sat:
        model = solver.model()
        order_val = [model.evaluate(order[i]).as_long() for i in range(6)]
        e0_val = model.evaluate(e0).as_long()
        e1_val = model.evaluate(e1).as_long()
        e2_val = model.evaluate(e2).as_long()
        e3_val = model.evaluate(e3).as_long()
        e4_val = model.evaluate(e4).as_long()
        e5_val = model.evaluate(e5).as_long()
        
        # Compute start days for each city in the order
        starts = [1, e0_val, e1_val, e2_val, e3_val, e4_val]
        ends = [e0_val, e1_val, e2_val, e3_val, e4_val, e5_val]
        
        itinerary = []
        for i in range(6):
            city_index = order_val[i]
            start = starts[i]
            end = ends[i]
            day_range = f"Day {start}-{end}"
            itinerary.append({
                "day_range": day_range,
                "place": city_names[city_index]
            })
        
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('No solution found')

if __name__ == '__main__':
    main()