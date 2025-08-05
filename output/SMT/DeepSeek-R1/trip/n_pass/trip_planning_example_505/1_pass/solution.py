from z3 import *
import json

def main():
    # Define the cities and their enum sort
    cities_enum = ['Prague', 'Stuttgart', 'Split', 'Krakow', 'Florence']
    City, (Prague, Stuttgart, Split, Krakow, Florence) = EnumSort('City', cities_enum)
    city_dict_const = {name: const for name, const in zip(cities_enum, [Prague, Stuttgart, Split, Krakow, Florence])}
    
    # Define the direct flight connections (as undirected edges)
    edges_by_name = [
        ('Stuttgart', 'Split'),
        ('Prague', 'Florence'),
        ('Krakow', 'Stuttgart'),
        ('Krakow', 'Split'),
        ('Split', 'Prague'),
        ('Krakow', 'Prague')
    ]
    edge_consts = []
    for a, b in edges_by_name:
        edge_consts.append((city_dict_const[a], city_dict_const[b]))
    
    allowed_pairs = []
    for (a, b) in edge_consts:
        allowed_pairs.append((a, b))
        allowed_pairs.append((b, a))
    
    # Create variables for the sequence: s0 (start) to s8 (end of day 8)
    s = [Const(f's{i}', City) for i in range(9)]
    
    solver = Solver()
    
    # Flight constraints: if we change city, the pair must be in allowed_pairs
    for i in range(1, 9):
        x = s[i-1]
        y = s[i]
        flight_ok = Or([And(x == a, y == b) for (a, b) in allowed_pairs])
        solver.add(Or(x == y, flight_ok))
    
    # Count the days per city
    cities_list = [Prague, Stuttgart, Split, Krakow, Florence]
    counts = [0]*5
    for idx, city in enumerate(cities_list):
        total = 0
        for i in range(1, 9):  # for each day from 1 to 8
            # Condition: start in the city OR (end in the city and start not in the city)
            cond = Or(s[i-1] == city, And(s[i] == city, s[i-1] != city))
            total += If(cond, 1, 0)
        counts[idx] = total
    
    # Add constraints for the required days per city
    solver.add(counts[0] == 4)  # Prague: 4 days
    solver.add(counts[1] == 2)  # Stuttgart: 2 days
    solver.add(counts[2] == 2)  # Split: 2 days
    solver.add(counts[3] == 2)  # Krakow: 2 days
    solver.add(counts[4] == 2)  # Florence: 2 days
    
    # Event constraints
    # Stuttgart on day 2: s[1] OR s[2] must be Stuttgart
    solver.add(Or(s[1] == Stuttgart, s[2] == Stuttgart))
    # Stuttgart on day 3: s[2] OR s[3] must be Stuttgart
    solver.add(Or(s[2] == Stuttgart, s[3] == Stuttgart))
    # Split on day 3: s[2] OR s[3] must be Split
    solver.add(Or(s[2] == Split, s[3] == Split))
    # Split on day 4: s[3] OR s[4] must be Split
    solver.add(Or(s[3] == Split, s[4] == Split))
    
    # Check for a solution
    if solver.check() == sat:
        m = solver.model()
        s_val = [m.evaluate(s[i]) for i in range(9)]
        
        # Map Z3 constants back to city names
        const_to_name = {const: name for name, const in city_dict_const.items()}
        
        itinerary = []
        for day in range(1, 9):  # days 1 to 8
            start_city = s_val[day-1]
            end_city = s_val[day]
            start_city_name = const_to_name[start_city]
            if start_city == end_city:
                cities_of_day = [start_city_name]
            else:
                end_city_name = const_to_name[end_city]
                cities_of_day = [start_city_name, end_city_name]
            itinerary.append({"day": day, "cities": cities_of_day})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()