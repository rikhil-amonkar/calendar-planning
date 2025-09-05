#!/usr/bin/env python3
import json
from z3 import *

def main():
    # Cities (indexed 0 to 9) and their planned durations:
    # 0: Warsaw (4 days)
    # 1: Venice (3 days)
    # 2: Vilnius (3 days)
    # 3: Salzburg (4 days) -- wedding must be attended between Day 22 and 25
    # 4: Amsterdam (2 days)
    # 5: Barcelona (5 days) -- meet friends between Day 2 and 6
    # 6: Paris (2 days) -- workshop between Day 1 and 2
    # 7: Hamburg (4 days) -- conference between Day 19 and 22
    # 8: Florence (5 days)
    # 9: Tallinn (2 days) -- friend meeting between Day 11 and 12
    city_names = ["Warsaw", "Venice", "Vilnius", "Salzburg", "Amsterdam", "Barcelona", "Paris", "Hamburg", "Florence", "Tallinn"]
    num_cities = 10
    
    # Create Z3 integer variables for the permutation order and start day for each city visit.
    order_vars = [Int(f"order{i}") for i in range(num_cities)]
    s_vars = [Int(f"s{i}") for i in range(num_cities)]
    
    solver = Solver()
    
    # Function to return the planned duration for a city (as a Z3 expression) based on its index.
    def duration_expr(city):
        return If(city == 0, 4,
               If(city == 1, 3,
               If(city == 2, 3,
               If(city == 3, 4,
               If(city == 4, 2,
               If(city == 5, 5,
               If(city == 6, 2,
               If(city == 7, 4,
               If(city == 8, 5,
               If(city == 9, 2, 0))))))))))
    
    # Domain constraints:
    for i in range(num_cities):
        solver.add(order_vars[i] >= 0, order_vars[i] < num_cities)
        solver.add(s_vars[i] >= 1, s_vars[i] <= 25)
    
    # The order must be a permutation of the 10 cities.
    solver.add(Distinct(order_vars))
    
    # Set the start day of the first city.
    solver.add(s_vars[0] == 1)
    
    # For consecutive visits, if you fly from city A to city B on day X then:
    # s_{i+1} = s_i + (duration of city at position i) - 1.
    for i in range(num_cities - 1):
        solver.add(s_vars[i+1] == s_vars[i] + duration_expr(order_vars[i]) - 1)
    
    # The end day (last day in the final city) must equal Day 25.
    solver.add(s_vars[num_cities - 1] + duration_expr(order_vars[num_cities - 1]) - 1 == 25)
    
    # Allowed direct flights (most are bidirectional except "from Tallinn to Vilnius"):
    allowed_pairs = []
    def add_bidirectional(a, b):
        allowed_pairs.append((a, b))
        allowed_pairs.append((b, a))
    # Paris and Venice
    add_bidirectional(6, 1)
    # Barcelona and Amsterdam
    add_bidirectional(5, 4)
    # Amsterdam and Warsaw
    add_bidirectional(4, 0)
    # Amsterdam and Vilnius
    add_bidirectional(4, 2)
    # Barcelona and Warsaw
    add_bidirectional(5, 0)
    # Warsaw and Venice
    add_bidirectional(0, 1)
    # Amsterdam and Hamburg
    add_bidirectional(4, 7)
    # Barcelona and Hamburg
    add_bidirectional(5, 7)
    # Barcelona and Florence
    add_bidirectional(5, 8)
    # Barcelona and Venice
    add_bidirectional(5, 1)
    # Paris and Hamburg
    add_bidirectional(6, 7)
    # Paris and Vilnius
    add_bidirectional(6, 2)
    # Paris and Amsterdam
    add_bidirectional(6, 4)
    # Paris and Florence
    add_bidirectional(6, 8)
    # Florence and Amsterdam
    add_bidirectional(8, 4)
    # Vilnius and Warsaw
    add_bidirectional(2, 0)
    # Barcelona and Tallinn
    add_bidirectional(5, 9)
    # Paris and Warsaw
    add_bidirectional(6, 0)
    # Tallinn and Warsaw
    add_bidirectional(9, 0)
    # Directional: from Tallinn to Vilnius (only allowed in this direction)
    allowed_pairs.append((9, 2))
    # Amsterdam and Tallinn
    add_bidirectional(4, 9)
    # Paris and Tallinn
    add_bidirectional(6, 9)
    # Paris and Barcelona
    add_bidirectional(6, 5)
    # Venice and Hamburg
    add_bidirectional(1, 7)
    # Warsaw and Hamburg
    add_bidirectional(0, 7)
    # Hamburg and Salzburg
    add_bidirectional(7, 3)
    # Amsterdam and Venice
    add_bidirectional(4, 1)
    
    # For a flight from city A to city B to be allowed, the pair must be in allowed_pairs.
    def allowed_flight(a, b):
        return Or([And(a == x, b == y) for (x, y) in allowed_pairs])
    
    # Add flight connectivity constraints for consecutive cities in the itinerary.
    for i in range(num_cities - 1):
        solver.add(allowed_flight(order_vars[i], order_vars[i+1]))
    
    # Event time constraints:
    for i in range(num_cities):
        # Workshop in Paris must be attended between Day 1 and 2.
        solver.add(Implies(order_vars[i] == 6, Or(s_vars[i] == 1, s_vars[i] == 2)))
        # Wedding in Salzburg (4-day visit) must include a day between Day 22 and 25.
        # This forces the start day s to be between 19 and 22 (since s+3 is the last day).
        solver.add(Implies(order_vars[i] == 3, And(s_vars[i] >= 19, s_vars[i] <= 22)))
        # Meet friends in Barcelona between Day 2 and 6.
        # For a 5-day block [s, s+4] to intersect [2,6], we require s <= 6.
        solver.add(Implies(order_vars[i] == 5, s_vars[i] <= 6))
        # Conference in Hamburg (4-day visit) between Day 19 and 22:
        # For block [s, s+3] to intersect [19,22], require s >= 16.
        solver.add(Implies(order_vars[i] == 7, s_vars[i] >= 16))
        # Friend meeting in Tallinn between Day 11 and 12:
        # For a 2-day block [s, s+1] to intersect [11,12], require s between 10 and 12.
        solver.add(Implies(order_vars[i] == 9, And(s_vars[i] >= 10, s_vars[i] <= 12)))
    
    # Check for a solution and extract the itinerary.
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(num_cities):
            city_val = model.evaluate(order_vars[i]).as_long()
            start_day = model.evaluate(s_vars[i]).as_long()
            # Fixed durations based on the city index.
            if city_val == 0:
                dur = 4
            elif city_val == 1:
                dur = 3
            elif city_val == 2:
                dur = 3
            elif city_val == 3:
                dur = 4
            elif city_val == 4:
                dur = 2
            elif city_val == 5:
                dur = 5
            elif city_val == 6:
                dur = 2
            elif city_val == 7:
                dur = 4
            elif city_val == 8:
                dur = 5
            elif city_val == 9:
                dur = 2
            end_day = start_day + dur - 1
            itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city_names[city_val]})
        output = {"itinerary": itinerary}
        print(json.dumps(output))
    else:
        # If no itinerary is found, output an empty itinerary.
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()