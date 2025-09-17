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
        solver.add(z3.And(order[i] >= 0, order[i] <= 5))
    solver.add(z3.Distinct(order))
    
    # Cumulative end days for each segment
    e = [z3.Int(f'e{i}') for i in range(6)]
    
    # Helper function to get days required using Z3 expressions
    def get_days(city_idx):
        return z3.If(city_idx == 0, days_req[0],
                z3.If(city_idx == 1, days_req[1],
                z3.If(city_idx == 2, days_req[2],
                z3.If(city_idx == 3, days_req[3],
                z3.If(city_idx == 4, days_req[4], days_req[5])))))
    
    # Constraints for cumulative end days
    solver.add(e[0] == get_days(order[0]))
    for i in range(1, 6):
        solver.add(e[i] == e[i-1] + get_days(order[i]))
    solver.add(e[5] == 21)  # Total days is sum of days_req
    
    # Munich must be at index 2, 3, or 4
    solver.add(z3.Or(order[2] == Munich, order[3] == Munich, order[4] == Munich))
    
    # Start day for a city at index i
    def start_day(i):
        if i == 0:
            return 1
        else:
            return e[i-1] + 1
    
    # Milan must be exactly on days 11-13
    milan_constraints = []
    for i in range(6):
        milan_constraints.append(z3.And(
            order[i] == Milan,
            start_day(i) == 11,
            e[i] == 13  # End day for Milan is 13
        ))
    solver.add(z3.Or(milan_constraints))
    
    # Krakow must be exactly on days 8-9
    krakow_constraints = []
    for i in range(6):
        krakow_constraints.append(z3.And(
            order[i] == Krakow,
            start_day(i) == 8,
            e[i] == 9  # End day for Krakow is 9
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
        e_val = [model.evaluate(e[i]).as_long() for i in range(6)]
        
        # Compute start days for each city in the order
        starts = [1]
        for i in range(1, 6):
            starts.append(e_val[i-1] + 1)
        ends = e_val
        
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