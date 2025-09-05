from z3 import *
import json

def main():
    # City codes and names:
    # 0: Hamburg (7 days)
    # 1: Munich (6 days)
    # 2: Manchester (2 days)
    # 3: Lyon (2 days)
    # 4: Split (7 days)
    city_names = {0: "Hamburg", 1: "Munich", 2: "Manchester", 3: "Lyon", 4: "Split"}
    
    # Duration function: returns required days for a given city code.
    def duration(city):
        return If(city == 0, 7,
               If(city == 1, 6,
               If(city == 2, 2,
               If(city == 3, 2, 7))))
    
    # Allowed flight predicate: returns True if there is a direct flight from x to y.
    def allowed_edge(x, y):
        return Or(
            And(x == 0, y == 2),   # Hamburg <-> Manchester
            And(x == 2, y == 0),
            And(x == 0, y == 1),   # Hamburg <-> Munich
            And(x == 1, y == 0),
            And(x == 4, y == 3),   # Split <-> Lyon
            And(x == 3, y == 4),
            And(x == 1, y == 2),   # Munich <-> Manchester
            And(x == 2, y == 1),
            And(x == 0, y == 4),   # Hamburg <-> Split
            And(x == 4, y == 0),
            And(x == 1, y == 4),   # Munich <-> Split
            And(x == 4, y == 1),
            And(x == 3, y == 1),   # Lyon <-> Munich
            And(x == 1, y == 3),
            And(x == 2, y == 4)    # From Manchester to Split (directed)
        )
    
    s = Solver()
    
    # Create variables for the itinerary order (5 segments)
    itinerary = [Int("city_%d" % i) for i in range(5)]
    for city in itinerary:
        s.add(city >= 0, city <= 4)
    s.add(Distinct(itinerary))
    
    # Define segment start expression for each segment.
    # Rule: s0 = Day 1, and for i>=1, s_i = s_{i-1} + duration(city_{i-1}) - 1.
    s0_expr = 1
    s1_expr = duration(itinerary[0])
    s2_expr = s1_expr + duration(itinerary[1]) - 1
    s3_expr = s2_expr + duration(itinerary[2]) - 1
    s4_expr = s3_expr + duration(itinerary[3]) - 1
    s_expr = [s0_expr, s1_expr, s2_expr, s3_expr, s4_expr]
    
    # Final overall end day must be 20:
    final_end = s4_expr + duration(itinerary[4]) - 1
    s.add(final_end == 20)
    
    # Add flight connectivity constraints: There must be a direct flight between consecutive cities.
    for i in range(4):
        s.add(allowed_edge(itinerary[i], itinerary[i+1]))
    
    # Special schedule constraints:
    # The annual show in Lyon is from day 13 to day 14,
    # so if Lyon (city 3) is visited, its segment must start exactly on day 13.
    for i in range(5):
        s.add(Implies(itinerary[i] == 3, s_expr[i] == 13))
    
    # Visit relatives in Manchester between day 19 and day 20;
    # Manchester (city 2) has a 2-day stay so it must start on day 19.
    for i in range(5):
        s.add(Implies(itinerary[i] == 2, s_expr[i] == 19))
    
    # Solve the SMT constraints.
    if s.check() == sat:
        m = s.model()
        # Extract itinerary order.
        order = [m.evaluate(itinerary[i]).as_long() for i in range(5)]
        
        # Reconstruct the itinerary segments.
        segments = []
        current_day = 1
        for i in range(5):
            city_code = order[i]
            # Get the duration for the city.
            if city_code == 0:
                dur = 7
            elif city_code == 1:
                dur = 6
            elif city_code == 2:
                dur = 2
            elif city_code == 3:
                dur = 2
            elif city_code == 4:
                dur = 7
            start_day = current_day
            end_day = start_day + dur - 1
            segments.append({
                "day_range": "Day {}-{}".format(start_day, end_day),
                "place": city_names[city_code]
            })
            # Next segment starts on the same day as the flight day (overlap).
            if i < 4:
                current_day = end_day
        output = {"itinerary": segments}
        print(json.dumps(output))
    else:
        print(json.dumps({"error": "No valid itinerary found."}))

if __name__ == "__main__":
    main()