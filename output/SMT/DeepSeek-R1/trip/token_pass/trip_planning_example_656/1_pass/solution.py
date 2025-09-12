from z3 import *
import json

def main():
    # Define city names and index mapping
    cities = ['Reykjavik', 'Istanbul', 'Edinburgh', 'Oslo', 'Stuttgart', 'Bucharest']
    city_index = {name: idx for idx, name in enumerate(cities)}
    required_days = [5, 4, 5, 2, 3, 5]

    # Direct flights: list of pairs of city names, then convert to indices
    direct_flights_names = [
        ('Bucharest', 'Oslo'),
        ('Istanbul', 'Oslo'),
        ('Reykjavik', 'Stuttgart'),
        ('Bucharest', 'Istanbul'),
        ('Stuttgart', 'Edinburgh'),
        ('Istanbul', 'Edinburgh'),
        ('Oslo', 'Reykjavik'),
        ('Istanbul', 'Stuttgart'),
        ('Oslo', 'Edinburgh')
    ]

    direct_flights_set = set()
    for (a, b) in direct_flights_names:
        i1 = city_index[a]
        i2 = city_index[b]
        direct_flights_set.add((i1, i2))
        direct_flights_set.add((i2, i1))

    # Create solver
    s = Solver()

    # Define the order variables: 6 integers for the positions
    order = [Int('o%d' % i) for i in range(6)]

    # Each element in order must be between 0 and 5 and distinct
    for i in range(6):
        s.add(order[i] >= 0, order[i] < 6)
    s.add(Distinct(order))

    # Define start and end for each city (by index)
    start = [Int('start_%d' % i) for i in range(6)]
    end = [Int('end_%d' % i) for i in range(6)]

    # Constraints for the first and last in the order
    s.add(start[order[0]] == 1)
    s.add(end[order[5]] == 19)

    # Constraints for consecutive cities in the order
    for i in range(5):
        s.add(end[order[i]] == start[order[i+1]])

    # Constraints for the required days for each city
    for i in range(6):
        s.add(end[i] - start[i] + 1 == required_days[i])
        s.add(start[i] >= 1)
        s.add(end[i] <= 19)

    # Constraints for direct flights between consecutive cities
    for i in range(5):
        city_i = order[i]
        city_j = order[i+1]
        constraints = []
        for (a, b) in direct_flights_set:
            constraints.append(And(city_i == a, city_j == b))
        s.add(Or(constraints))

    # Constraints for Istanbul (index1) and Oslo (index3)
    s.add(start[1] <= 8)   # Istanbul
    s.add(end[1] >= 5)     # Istanbul
    s.add(start[3] <= 8)   # Oslo
    s.add(end[3] >= 9)     # Oslo

    # Check and get model
    if s.check() == sat:
        m = s.model()
        # Extract the order
        order_val = [m.evaluate(order[i]).as_long() for i in range(6)]
        # For each city in the order, get its start and end days
        itinerary_list = []
        for pos in range(6):
            city_idx = order_val[pos]
            city_name = cities[city_idx]
            s_val = m.evaluate(start[city_idx]).as_long()
            e_val = m.evaluate(end[city_idx]).as_long()
            # Format the day range string
            if s_val == e_val:
                day_range_str = f"Day {s_val}"
            else:
                day_range_str = f"Day {s_val}-{e_val}"
            itinerary_list.append({"day_range": day_range_str, "place": city_name})

        # Output as JSON
        result = {"itinerary": itinerary_list}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()