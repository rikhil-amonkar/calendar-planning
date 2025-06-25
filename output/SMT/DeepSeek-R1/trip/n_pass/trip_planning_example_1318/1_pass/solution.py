from z3 import *

def main():
    # City IDs and names
    cities = ["Oslo", "Helsinki", "Edinburgh", "Riga", "Tallinn", "Budapest", "Vilnius", "Porto", "Geneva"]
    # Map: name to id
    city_to_id = {name: idx for idx, name in enumerate(cities)}
    # Lengths for each city id: [0,1,2,3,4,5,6,7,8]
    lengths = [2, 2, 3, 2, 5, 5, 5, 5, 4]
    
    # Build the directed flight graph
    bidirectional_pairs = [
        (7, 0),  # Porto and Oslo
        (2, 5),  # Edinburgh and Budapest
        (2, 8),  # Edinburgh and Geneva
        (2, 7),  # Edinburgh and Porto
        (6, 1),  # Vilnius and Helsinki
        (3, 0),  # Riga and Oslo
        (8, 0),  # Geneva and Oslo
        (2, 0),  # Edinburgh and Oslo
        (2, 1),  # Edinburgh and Helsinki
        (6, 0),  # Vilnius and Oslo
        (3, 1),  # Riga and Helsinki
        (5, 8),  # Budapest and Geneva
        (1, 5),  # Helsinki and Budapest
        (1, 0),  # Helsinki and Oslo
        (2, 3),  # Edinburgh and Riga
        (4, 1),  # Tallinn and Helsinki
        (8, 7),  # Geneva and Porto
        (5, 0),  # Budapest and Oslo
        (1, 8),  # Helsinki and Geneva
        (4, 0)   # Tallinn and Oslo
    ]
    one_way = [
        (3, 4),  # Riga to Tallinn
        (4, 6),  # Tallinn to Vilnius
        (3, 6)   # Riga to Vilnius
    ]
    
    edges = set()
    for (a, b) in bidirectional_pairs:
        edges.add((a, b))
        edges.add((b, a))
    for (a, b) in one_way:
        edges.add((a, b))
    
    # Create Z3 variables for the order: o0 to o8
    o = [Int('o%d' % i) for i in range(9)]
    
    s = Solver()
    
    # Each o[i] is between 0 and 8
    for i in range(9):
        s.add(And(o[i] >= 0, o[i] < 9))
    s.add(Distinct(o))
    
    # Helper function to get the length of a city given its Z3 integer variable
    def get_length(city_var):
        cases = []
        for j in range(9):
            cases.append((city_var == j, lengths[j]))
        expr = cases[0][1]
        for i in range(1, 9):
            expr = If(cases[i][0], cases[i][1], expr)
        return expr
    
    # Build cumulative sums: cum[0]=0, cum[i] for i in 1..9
    cum = [0] * 10
    cum[0] = 0
    for i in range(1, 10):
        # cum[i] = cum[i-1] + length of o[i-1]
        cum[i] = cum[i-1] + get_length(o[i-1])
    
    # Find the position of Oslo (id=0) in the order
    j_Oslo = o[0]
    j_Oslo = If(o[0] == 0, 0, 
              If(o[1] == 0, 1,
              If(o[2] == 0, 2,
              If(o[3] == 0, 3,
              If(o[4] == 0, 4,
              If(o[5] == 0, 5,
              If(o[6] == 0, 6,
              If(o[7] == 0, 7,
              8)))))))
    
    # Find the position of Tallinn (id=4)
    j_Tallinn = o[0]
    j_Tallinn = If(o[0] == 4, 0,
                 If(o[1] == 4, 1,
                 If(o[2] == 4, 2,
                 If(o[3] == 4, 3,
                 If(o[4] == 4, 4,
                 If(o[5] == 4, 5,
                 If(o[6] == 4, 6,
                 If(o[7] == 4, 7,
                 8)))))))
    
    # Start day for Oslo: cum[j_Oslo] - j_Oslo + 1
    start_Oslo = cum[j_Oslo] - j_Oslo + 1
    start_Tallinn = cum[j_Tallinn] - j_Tallinn + 1
    
    s.add(Or(start_Oslo == 23, start_Oslo == 24))
    s.add(And(start_Tallinn >= 1, start_Tallinn <= 8))
    
    # Flight constraints: for i in 0 to 7, (o[i], o[i+1]) must be in edges
    for i in range(8):
        constraints_i = []
        for edge in edges:
            a, b = edge
            constraints_i.append(And(o[i] == a, o[i+1] == b))
        s.add(Or(constraints_i))
    
    # Solve
    if s.check() == sat:
        model = s.model()
        order_val = [model.evaluate(o[i]).as_long() for i in range(9)]
        print("Found a valid itinerary:")
        print("Order of cities:", [cities[idx] for idx in order_val])
        
        # Build the itinerary
        itinerary = []
        current_start = 1
        for i in range(9):
            city_id = order_val[i]
            city_name = cities[city_id]
            L = lengths[city_id]
            end_day = current_start + L - 1
            
            # Entire stay block
            if current_start == end_day:
                day_range_str = f"Day {current_start}"
            else:
                day_range_str = f"Day {current_start}-{end_day}"
            itinerary.append({"day_range": day_range_str, "place": city_name})
            
            # If not the last city, add flight day records
            if i < 8:
                # Departure from current city on end_day
                itinerary.append({"day_range": f"Day {end_day}", "place": city_name})
                # Arrival at next city on end_day
                next_city_id = order_val[i+1]
                next_city_name = cities[next_city_id]
                itinerary.append({"day_range": f"Day {end_day}", "place": next_city_name})
            
            current_start = end_day  # Next city starts on the same day
        
        # Output as JSON
        import json
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()