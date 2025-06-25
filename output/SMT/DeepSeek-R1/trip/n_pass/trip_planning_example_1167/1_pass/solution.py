from z3 import *
import json

def main():
    # Define city indices
    cities = ["Dublin", "Krakow", "Istanbul", "Venice", "Naples", "Brussels", "Mykonos", "Frankfurt"]
    days_req = [5, 4, 3, 3, 4, 2, 4, 3]  # corresponding days required for each city

    # Build the directed flights list
    pairs_by_index = [
        (0, 5), (6, 4), (3, 2), (7, 1), (4, 0), (1, 5), (4, 2), (4, 5), (2, 7),  # 0 to 8
        (5, 7),  # index9: directional (Brussels to Frankfurt)
        (2, 1), (2, 5), (3, 7), (4, 7), (0, 1), (3, 5), (4, 3), (2, 0), (3, 0), (0, 7)  # 10 to 19
    ]
    directed_flights_list = []
    for idx, (a, b) in enumerate(pairs_by_index):
        if idx == 9:
            directed_flights_list.append((a, b))
        else:
            directed_flights_list.append((a, b))
            directed_flights_list.append((b, a))

    # Create Z3 variables
    s = [Int(f's_{i}') for i in range(8)]  # start day for the city at position i
    e = [Int(f'e_{i}') for i in range(8)]  # end day for the city at position i
    order = [Int(f'order_{i}') for i in range(8)]  # city index at position i

    s0 = Solver()

    # Order must be a permutation of 0 to 7
    s0.add(Distinct(order))
    for i in range(8):
        s0.add(order[i] >= 0, order[i] < 8)

    # Start and end day constraints
    for i in range(8):
        # Lookup required days for the city at position i
        days_i = Int(f'days_i_{i}')
        s0.add(days_i == If(order[i] == 0, days_req[0],
                          If(order[i] == 1, days_req[1],
                          If(order[i] == 2, days_req[2],
                          If(order[i] == 3, days_req[3],
                          If(order[i] == 4, days_req[4],
                          If(order[i] == 5, days_req[5],
                          If(order[i] == 6, days_req[6],
                          days_req[7]))))))))
        if i == 0:
            s0.add(s[i] == 1)
        else:
            s0.add(s[i] == e[i-1])
        s0.add(e[i] == s[i] + days_i - 1)
        s0.add(s[i] >= 1, s[i] <= 21)
        s0.add(e[i] >= 1, e[i] <= 21)

    s0.add(e[7] == 21)  # total trip ends at day 21

    # Fixed events
    for i in range(8):
        # Dublin (index0) must be from day 11 to 15
        s0.add(If(order[i] == 0, And(s[i] == 11, e[i] == 15), True))
        # Mykonos (index6): at least one day in [1,4] -> start <= 4
        s0.add(If(order[i] == 6, s[i] <= 4, True))
        # Istanbul (index2): at least one day in [9,11] -> s[i] <= 11 and e[i] >= 9
        s0.add(If(order[i] == 2, And(s[i] <= 11, e[i] >= 9), True))
        # Frankfurt (index7): at least one day in [15,17] -> s[i] <= 17 and e[i] >= 15
        s0.add(If(order[i] == 7, And(s[i] <= 17, e[i] >= 15), True))

    # Flight constraints for consecutive cities
    for i in range(7):
        conds = []
        for (a, b) in directed_flights_list:
            conds.append(And(order[i] == a, order[i+1] == b))
        s0.add(Or(conds))

    # Solve the model
    if s0.check() == sat:
        model = s0.model()
        # Extract the order, start, and end days
        order_val = [model.evaluate(order[i]).as_long() for i in range(8)]
        s_val = [model.evaluate(s[i]).as_long() for i in range(8)]
        e_val = [model.evaluate(e[i]).as_long() for i in range(8)]
        
        # Build itinerary
        itinerary = []
        for i in range(8):
            city_index = order_val[i]
            city_name = cities[city_index]
            # Add the contiguous stay block
            if s_val[i] == e_val[i]:
                day_range_str = f"Day {s_val[i]}"
            else:
                day_range_str = f"Day {s_val[i]}-{e_val[i]}"
            itinerary.append({"day_range": day_range_str, "place": city_name})
            
            # If not the last city, add flight day records
            if i < 7:
                next_city_index = order_val[i+1]
                next_city_name = cities[next_city_index]
                itinerary.append({"day_range": f"Day {e_val[i]}", "place": city_name})
                itinerary.append({"day_range": f"Day {e_val[i]}", "place": next_city_name})
        
        # Output as JSON
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()