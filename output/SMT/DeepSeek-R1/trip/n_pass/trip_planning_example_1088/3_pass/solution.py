import json
from z3 import *

def main():
    cities = ["Reykjavik", "Stockholm", "Tallinn", "Oslo", "Split", "Geneva", "Porto", "Stuttgart"]
    days_req = [2, 3, 5, 5, 3, 2, 3, 5]  # for cities in order of index

    # Define direct flights as a set of tuples (both directions)
    graph_edges = [
        (0, 1), (0, 2), (0, 3), (0, 7),
        (1, 0), (1, 3), (1, 4), (1, 5), (1, 7),
        (2, 0), (2, 3),
        (3, 0), (3, 1), (3, 2), (3, 4), (3, 5), (3, 6),
        (4, 1), (4, 3), (4, 5), (4, 7),
        (5, 1), (5, 3), (5, 4), (5, 6),
        (6, 3), (6, 5), (6, 7),
        (7, 0), (7, 1), (7, 4), (7, 6)
    ]
    allowed_edges = set(graph_edges)

    s = Solver()

    # Order of cities: list of integers for positions 0 to 7
    order = [Int('order_%d' % i) for i in range(8)]
    
    # Each order[i] must be between 0 and 7
    for i in range(8):
        s.add(order[i] >= 0, order[i] < 8)
    
    s.add(Distinct(order))
    
    # First city is Reykjavik (0), last is Porto (6)
    s.add(order[0] == 0)
    s.add(order[7] == 6)
    
    # Flight constraints: consecutive cities must have a direct flight
    for i in range(7):
        cons = []
        for u, v in allowed_edges:
            cons.append(And(order[i] == u, order[i+1] == v))
        s.add(Or(cons))
    
    # Helper function to get required days for a city (symbolic variable)
    def get_days(city_var):
        return If(city_var == 0, days_req[0],
               If(city_var == 1, days_req[1],
               If(city_var == 2, days_req[2],
               If(city_var == 3, days_req[3],
               If(city_var == 4, days_req[4],
               If(city_var == 5, days_req[5],
               If(city_var == 6, days_req[6],
               days_req[7])))))))
    
    # Timeline variables
    s_arr = [Int('s_arr_%d' % i) for i in range(8)]
    e_arr = [Int('e_arr_%d' % i) for i in range(8)]
    
    # Fixed timeline for Reykjavik (first city)
    s.add(s_arr[0] == 1)
    s.add(e_arr[0] == s_arr[0] + get_days(order[0]) - 1)
    
    # Chain the cities: each city starts when the previous ends
    for p in range(1, 8):
        s.add(s_arr[p] == e_arr[p-1])
        s.add(e_arr[p] == s_arr[p] + get_days(order[p]) - 1)
    
    # The trip must end at day 21
    s.add(e_arr[7] == 21)
    
    # Porto (city index 6) must start on day 19 (since it ends on day 21 and lasts 3 days)
    s.add(s_arr[7] == 19)
    
    # Stockholm (city index 1) must have a start day between 2 and 4 inclusive
    stockholm_constraints = []
    for i in range(8):
        # If the city at position i is Stockholm, then its start day must be between 2 and 4
        stockholm_constraints.append(And(order[i] == 1, s_arr[i] >= 2, s_arr[i] <= 4))
    s.add(Or(stockholm_constraints))
    
    # Check and get model
    if s.check() == sat:
        model = s.model()
        order_vals = [model.evaluate(order[i]).as_long() for i in range(8)]
        s_vals = [model.evaluate(s_arr[i]).as_long() for i in range(8)]
        e_vals = [model.evaluate(e_arr[i]).as_long() for i in range(8)]
        
        itinerary = []
        for day in range(1, 22):  # days 1 to 21
            cities_on_day = []
            for pos in range(8):
                if s_vals[pos] <= day <= e_vals[pos]:
                    cities_on_day.append((pos, cities[order_vals[pos]]))
            # Sort by position in the itinerary
            cities_on_day_sorted = sorted(cities_on_day, key=lambda x: x[0])
            place_str = ", ".join(city for (_, city) in cities_on_day_sorted)
            itinerary.append({"day": day, "place": place_str})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()