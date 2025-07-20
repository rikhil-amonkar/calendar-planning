from z3 import *

def main():
    # Define city mapping and durations
    city_map = {
        'Prague': 0, 'Warsaw': 1, 'Dublin': 2, 'Athens': 3, 'Vilnius': 4, 'Porto': 5,
        'London': 6, 'Seville': 7, 'Lisbon': 8, 'Dubrovnik': 9
    }
    dur = [3, 4, 3, 3, 4, 5, 3, 2, 5, 3]  # durations for cities 0 to 9

    # Define flight connections (bidirectional)
    edges_str = [
        "Warsaw and Vilnius", "Prague and Athens", "London and Lisbon", "Lisbon and Porto",
        "Prague and Lisbon", "London and Dublin", "Athens and Vilnius", "Athens and Dublin",
        "Prague and London", "London and Warsaw", "Dublin and Seville", "Seville and Porto",
        "Lisbon and Athens", "Dublin and Porto", "Athens and Warsaw", "Lisbon and Warsaw",
        "Porto and Warsaw", "Prague and Warsaw", "Prague and Dublin", "Athens and Dubrovnik",
        "Lisbon and Dublin", "Dubrovnik and Dublin", "Lisbon and Seville", "London and Athens"
    ]
    flight_set = set()
    for s in edges_str:
        c1, c2 = s.split(' and ')
        i, j = city_map[c1], city_map[c2]
        flight_set.add((i, j))
        flight_set.add((j, i))

    # Initialize Z3 solver
    s = Solver()

    # Define order variables
    order = [Int(f'order_{i}') for i in range(10)]
    for i in range(10):
        s.add(order[i] >= 0, order[i] < 10)
    s.add(Distinct(order))

    # Define position array
    pos = Array('pos', IntSort(), IntSort())
    for k in range(10):
        s.add(pos[order[k]] == k)

    # Define start days for each city
    start = [Int(f'start_{c}') for c in range(10)]
    for c in range(10):
        sum_expr = 1
        for d in range(10):
            cond = (pos[d] < pos[c])
            sum_expr = sum_expr + If(cond, dur[d] - 1, 0)
        s.add(start[c] == sum_expr)

    # Add constraints for specific cities
    s.add(start[city_map['Lisbon']] == 5)    # Lisbon starts on day 5
    s.add(start[city_map['Porto']] == 16)    # Porto starts on day 16
    s.add(start[city_map['Prague']] <= 3)    # Prague starts by day 3
    s.add(start[city_map['Warsaw']] >= 17, start[city_map['Warsaw']] <= 23)  # Warsaw starts between days 17-23

    # Add flight constraints between consecutive cities
    for k in range(9):
        a, b = order[k], order[k+1]
        s.add(Or([And(a == i, b == j) for (i, j) in flight_set]))

    # Check for a solution
    if s.check() == sat:
        m = s.model()
        order_val = [m.evaluate(order[i]).as_long() for i in range(10)]
        start_val = [m.evaluate(start[c]).as_long() for c in range(10)]
        
        # Generate itinerary
        city_names = {v: k for k, v in city_map.items()}
        itinerary = []
        for idx, c in enumerate(order_val):
            name = city_names[c]
            S = start_val[c]
            E = S + dur[c] - 1
            itinerary.append({"day_range": f"Day {S}-{E}", "place": name})
            if idx < 9:
                itinerary.append({"day_range": f"Day {E}", "place": name})
                next_city = order_val[idx+1]
                next_name = city_names[next_city]
                itinerary.append({"day_range": f"Day {E}", "place": next_name})
        
        # Output result
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == '__main__':
    main()