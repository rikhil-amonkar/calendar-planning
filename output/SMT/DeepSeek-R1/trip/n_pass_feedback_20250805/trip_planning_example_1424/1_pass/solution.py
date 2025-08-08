from z3 import *
import json

def main():
    # Define city names and their indices
    cities = ['Warsaw', 'Porto', 'Naples', 'Brussels', 'Split', 'Reykjavik', 'Amsterdam', 'Lyon', 'Helsinki', 'Valencia']
    city_to_index = {city: idx for idx, city in enumerate(cities)}
    index_to_city = {idx: city for idx, city in enumerate(cities)}
    
    # Required days per city
    required_days = [3, 5, 4, 3, 3, 5, 4, 3, 4, 2]  # Corresponding to cities order
    
    # Flight connections
    flight_strings = [
        "Amsterdam and Warsaw", "Helsinki and Brussels", "Helsinki and Warsaw", 
        "Reykjavik and Brussels", "Amsterdam and Lyon", "Amsterdam and Naples", 
        "Amsterdam and Reykjavik", "Naples and Valencia", "Porto and Brussels", 
        "Amsterdam and Split", "Lyon and Split", "Warsaw and Split", 
        "Porto and Amsterdam", "Helsinki and Split", "Brussels and Lyon", 
        "Porto and Lyon", "Reykjavik and Warsaw", "Brussels and Valencia", 
        "Valencia and Lyon", "Porto and Warsaw", "Warsaw and Valencia", 
        "Amsterdam and Helsinki", "Porto and Valencia", "Warsaw and Brussels", 
        "Warsaw and Naples", "Naples and Split", "Helsinki and Naples", 
        "Helsinki and Reykjavik", "Amsterdam and Valencia", "Naples and Brussels"
    ]
    
    flight_pairs_set = set()
    for s in flight_strings:
        parts = s.split(' and ')
        c1, c2 = parts[0], parts[1]
        i1, i2 = city_to_index[c1], city_to_index[c2]
        if i1 > i2:
            i1, i2 = i2, i1
        flight_pairs_set.add((i1, i2))
    
    # Precompute connected cities for each city
    connected = [[] for _ in range(10)]
    for (i, j) in flight_pairs_set:
        connected[i].append(j)
        connected[j].append(i)
    
    # Initialize Z3 solver and variables
    s = Solver()
    in_day_city = [[Bool('in_d%dc%d' % (d, c)) for c in range(10)] for d in range(27)]
    
    # Constraint: Each day has at least one and at most two cities
    for d in range(27):
        at_least_one = Or([in_day_city[d][c] for c in range(10)])
        s.add(at_least_one)
        # At most two: use PbLe (sum <= 2)
        bools = [in_day_city[d][c] for c in range(10)]
        s.add(PbLe([(b, 1) for b in bools], 2))
    
    # Constraint: Total days per city
    for c in range(10):
        total_days = Sum([If(in_day_city[d][c], 1, 0) for d in range(27)])
        s.add(total_days == required_days[c])
    
    # Event constraints
    # Porto: at least one day in [1,5] (days 0 to 4 in 0-indexed)
    s.add(Or([in_day_city[d][city_to_index['Porto']] for d in range(0,5)]))
    # Amsterdam: at least one day in [5,8] (days 4 to 7)
    s.add(Or([in_day_city[d][city_to_index['Amsterdam']] for d in range(4,8)]))
    # Helsinki: at least one day in [8,11] (days 7 to 10)
    s.add(Or([in_day_city[d][city_to_index['Helsinki']] for d in range(7,11)]))
    # Naples: must be present on days 17,18,19,20 (0-indexed: 16,17,18,19)
    for d in [16,17,18,19]:
        s.add(in_day_city[d][city_to_index['Naples']])
    # Brussels: must be present on days 20,21,22 (0-indexed: 19,20,21)
    for d in [19,20,21]:
        s.add(in_day_city[d][city_to_index['Brussels']])
    
    # Constraint: For each day, if two cities are present, they must be connected by a direct flight
    for d in range(27):
        for i in range(10):
            for j in range(i+1, 10):
                if (i, j) in flight_pairs_set:
                    continue
                s.add(Not(And(in_day_city[d][i], in_day_city[d][j])))
    
    # Constraint: Travel continuity between consecutive days
    for d in range(26):  # d from 0 to 25
        for i in range(10):
            # If leaving city i from day d to d+1
            cond1 = Implies(
                And(in_day_city[d][i], Not(in_day_city[d+1][i])),
                Or([in_day_city[d+1][j] for j in connected[i]])
            )
            s.add(cond1)
            # If arriving at city i on day d+1
            cond2 = Implies(
                And(in_day_city[d+1][i], Not(in_day_city[d][i])),
                Or([in_day_city[d][j] for j in connected[i]])
            )
            s.add(cond2)
    
    # Solve the constraints
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for d in range(27):
            cities_this_day = []
            for c in range(10):
                if is_true(model[in_day_city[d][c]]):
                    cities_this_day.append(index_to_city[c])
            itinerary.append({"day": d+1, "cities": cities_this_day})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()