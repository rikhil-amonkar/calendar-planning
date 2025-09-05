from z3 import *
import json

def main():
    s = Solver()
    
    # There are 8 segments (one per city visit) and the total trip length is 20 days.
    n = 8

    # Cities encoded as numbers:
    # 0: Oslo, 1: Reykjavik, 2: Stockholm, 3: Munich, 4: Frankfurt,
    # 5: Barcelona, 6: Bucharest, 7: Split
    cities = [Int(f"city_{i}") for i in range(n)]
    # Start and end days for each segment
    start = [Int(f"start_{i}") for i in range(n)]
    end = [Int(f"end_{i}") for i in range(n)]
    
    # Domain constraints for cities and days
    for i in range(n):
        s.add(cities[i] >= 0, cities[i] <= 7)
        s.add(start[i] >= 1, start[i] <= 20)
        s.add(end[i] >= 1, end[i] <= 20)
        
    # Each city is visited exactly once (a permutation)
    s.add(Distinct(cities))
    
    # Define the fixed durations for each city.
    # Oslo: 2 days, Reykjavik: 5 days, Stockholm: 4 days,
    # Munich: 4 days, Frankfurt: 4 days, Barcelona: 3 days,
    # Bucharest: 2 days, Split: 3 days.
    # When flying from one city to the next on the same day, that day counts for both.
    # So we define: end[i] = start[i] + (duration - 1)
    def city_duration_expr(city_var, start_var):
        return If(city_var == 0, start_var + 2 - 1,   # Oslo
               If(city_var == 1, start_var + 5 - 1,   # Reykjavik
               If(city_var == 2, start_var + 4 - 1,   # Stockholm
               If(city_var == 3, start_var + 4 - 1,   # Munich
               If(city_var == 4, start_var + 4 - 1,   # Frankfurt
               If(city_var == 5, start_var + 3 - 1,   # Barcelona
               If(city_var == 6, start_var + 2 - 1,   # Bucharest
               If(city_var == 7, start_var + 3 - 1,   # Split
                  start_var))))))))
    
    for i in range(n):
        s.add(end[i] == city_duration_expr(cities[i], start[i]))
    
    # Link the segments: if you fly on day X from city A to city B,
    # then you finish city A on day X and start city B on day X.
    s.add(start[0] == 1)
    for i in range(1, n):
        s.add(start[i] == end[i-1])
    
    # Total trip must end on day 20
    s.add(end[n-1] == 20)
    
    # Special time-event constraints.
    # If you are in Oslo (0), you must be there on days 16 and 17.
    # For a 2-day visit, that forces start == 16.
    for i in range(n):
        s.add(Implies(cities[i] == 0, start[i] == 16))
    
    # In Reykjavik (1) you spend 5 days and must meet a friend between day 9 and 13.
    for i in range(n):
        # Reykjavik segment: [start, start+4] must intersect [9, 13]
        s.add(Implies(cities[i] == 1, And(start[i] <= 13, end[i] >= 9)))
    
    # In Munich (3) you spend 4 days and visit relatives between day 13 and 16.
    for i in range(n):
        # Munich segment: [start, start+3] intersects [13,16]
        s.add(Implies(cities[i] == 3, And(start[i] <= 16, end[i] >= 13)))
    
    # In Frankfurt (4) you stay for 4 days and attend a workshop between day 17 and 20.
    for i in range(n):
        # Frankfurt segment: [start, start+3] intersects [17,20]
        s.add(Implies(cities[i] == 4, And(start[i] <= 20, end[i] >= 17)))
    
    # Flight connectivity constraints.
    # Only the following direct flights exist (bidirectional):
    allowed_pairs = [
        (1, 3), (3, 1),
        (3, 4), (4, 3),
        (7, 0), (0, 7),
        (1, 0), (0, 1),
        (6, 3), (3, 6),
        (0, 4), (4, 0),
        (6, 5), (5, 6),
        (5, 4), (4, 5),
        (1, 4), (4, 1),
        (5, 2), (2, 5),
        (5, 1), (1, 5),
        (2, 1), (1, 2),
        (5, 7), (7, 5),
        (6, 0), (0, 6),
        (6, 4), (4, 6),
        (7, 2), (2, 7),
        (5, 0), (0, 5),
        (2, 3), (3, 2),
        (2, 0), (0, 2),
        (7, 4), (4, 7),
        (5, 3), (3, 5),
        (2, 4), (4, 2),
        (3, 0), (0, 3),
        (7, 3), (3, 7)
    ]
    
    for i in range(n - 1):
        a = cities[i]
        b = cities[i+1]
        # Constraint: (a, b) must be one of the allowed pairs.
        allowed = []
        for (x, y) in allowed_pairs:
            allowed.append(And(a == x, b == y))
        s.add(Or(allowed))
    
    # Check for satisfiability and, if sat, extract the model.
    if s.check() == sat:
        m = s.model()
        city_names = {0:"Oslo", 1:"Reykjavik", 2:"Stockholm", 3:"Munich", 4:"Frankfurt", 5:"Barcelona", 6:"Bucharest", 7:"Split"}
        itinerary = []
        for i in range(n):
            city_val = m.evaluate(cities[i]).as_long()
            start_day = m.evaluate(start[i]).as_long()
            end_day = m.evaluate(end[i]).as_long()
            itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city_names[city_val]})
        output = {"itinerary": itinerary}
    else:
        output = {"error": "No solution found"}
    
    print(json.dumps(output))

if __name__ == "__main__":
    main()