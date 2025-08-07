from z3 import *
import json

def main():
    # Mapping cities to integers
    city_to_int = {
        'BRU': 0,  # Brussels
        'BUH': 1,  # Bucharest
        'STU': 2,  # Stuttgart
        'MYK': 3,  # Mykonos
        'HEL': 4,  # Helsinki
        'SPL': 5,  # Split
        'LON': 6,  # London
    }
    int_to_city = {v: k for k, v in city_to_int.items()}
    MAD = 7  # Madrid

    # Days required for each city (for the first 7 cities, index by the integer)
    days_arr = [4, 3, 4, 2, 5, 3, 5]  # [BRU, BUH, STU, MYK, HEL, SPL, LON]

    # Define the edge set for direct flights (each edge as (min, max))
    edge_set = {
        (0, 1), (0, 4), (0, 6), (0, 7),
        (1, 6), (1, 7),
        (2, 5), (2, 6),
        (3, 6), (3, 7),
        (4, 5), (4, 6), (4, 7),
        (5, 6), (5, 7),
        (6, 7)
    }

    s = Solver()

    # Create the sequence variables: 7 positions
    seq = [Int(f'seq_{i}') for i in range(7)]
    # Each element in seq must be between 0 and 6 (inclusive) and distinct
    s.add([And(seq[i] >= 0, seq[i] <= 6) for i in range(7)])
    s.add(Distinct(seq))

    # Define base[0..7] (base[0] to base[7] inclusive; base[7] is for after the last city in the 7)
    base = [Int(f'base_{i}') for i in range(8)]
    s.add(base[0] == 0)

    # Helper function to get days for a city (symbolic integer)
    def get_days(city_int):
        return If(city_int == 0, days_arr[0],
              If(city_int == 1, days_arr[1],
              If(city_int == 2, days_arr[2],
              If(city_int == 3, days_arr[3],
              If(city_int == 4, days_arr[4],
              If(city_int == 5, days_arr[5],
              If(city_int == 6, days_arr[6], 0)))))))

    # Constraints for base
    for i in range(7):
        s.add(base[i+1] == base[i] + (get_days(seq[i]) - 1))

    # Adjacency constraints for consecutive cities in the sequence
    def adj(a, b):
        conditions = []
        for edge in edge_set:
            x, y = edge
            cond = Or(And(a == x, b == y), And(a == y, b == x))
            conditions.append(cond)
        return Or(conditions)

    for i in range(6):
        s.add(adj(seq[i], seq[i+1]))
    # Constraint for the last city in the sequence to Madrid
    s.add(adj(seq[6], MAD))

    # Stuttgart constraint: must start by day 4
    STU_int = city_to_int['STU']  # which is 2
    start_STU = Int('start_STU')
    # Create a condition: if STU is at position i, then start_STU = 1 + base[i]
    or_conds = []
    for i in range(7):
        or_conds.append(And(seq[i] == STU_int, start_STU == 1 + base[i]))
    s.add(Or(or_conds))
    s.add(start_STU <= 4)

    # Check and get model
    if s.check() == sat:
        model = s.model()
        # Extract the sequence
        seq_val = []
        for i in range(7):
            c_val = model[seq[i]].as_long()
            seq_val.append(c_val)
        
        # Compute base_val (the actual values)
        base_val = [0] * 8
        for i in range(7):
            c = seq_val[i]
            d = days_arr[c]
            base_val[i+1] = base_val[i] + (d - 1)
        
        # Create list of cities with start and end days (first 7 cities)
        cities_info = []
        for i in range(7):
            start_day = 1 + base_val[i]
            end_day = 1 + base_val[i+1]   # inclusive
            city_name = int_to_city[seq_val[i]]
            cities_info.append( (start_day, end_day, city_name) )
        # Add Madrid
        cities_info.append( (20, 21, 'MAD') )
        
        # Build itinerary for each day (1 to 21)
        itinerary = []
        for d in range(1, 22):
            places = []
            for (s, e, name) in cities_info:
                if s <= d <= e:
                    places.append(name)
            places.sort()  # Sort alphabetically for consistent output
            itinerary.append( {"day": d, "place": places} )
        
        # Create the result dictionary
        result = { "itinerary": itinerary }
        # Output as JSON string
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()