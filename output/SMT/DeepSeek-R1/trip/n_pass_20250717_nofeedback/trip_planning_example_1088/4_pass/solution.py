import json
from z3 import *

def main():
    cities = ["Reykjavik", "Stockholm", "Tallinn", "Oslo", "Split", "Geneva", "Porto", "Stuttgart"]
    durations = [2, 3, 5, 5, 3, 2, 3, 5]  # for cities in order of index

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
    
    # Helper function to get duration for a city (symbolic variable)
    def get_duration(city_var):
        return If(city_var == 0, durations[0],
               If(city_var == 1, durations[1],
               If(city_var == 2, durations[2],
               If(city_var == 3, durations[3],
               If(city_var == 4, durations[4],
               If(city_var == 5, durations[5],
               If(city_var == 6, durations[6],
               durations[7]))))))
    
    # Timeline variables: start and end days for each position in the itinerary
    s_arr = [Int('s_arr_%d' % i) for i in range(8)]
    e_arr = [Int('e_arr_%d' % i) for i in range(8)]
    
    # Fixed timeline for the first city (Reykjavik)
    s.add(s_arr[0] == 1)
    s.add(e_arr[0] == s_arr[0] + get_duration(order[0]) - 1)
    
    # For positions 1 to 7: start day is the end day of the previous city
    for i in range(1, 8):
        s.add(s_arr[i] == e_arr[i-1])
        s.add(e_arr[i] == s_arr[i] + get_duration(order[i]) - 1)
    
    # The entire trip ends at day 21
    s.add(e_arr[7] == 21)
    
    # Porto must start on day 19 (since it lasts 3 days and ends on day 21)
    s.add(s_arr[7] == 19)
    
    # Stockholm must be visited between days 2 and 4 (inclusive)
    stockholm_constraints = []
    for i in range(1, 8):  # Stockholm cannot be at position0 (Reykjavik)
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
                    city_name = cities[order_vals[pos]]
                    cities_on_day.append((pos, city_name))
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