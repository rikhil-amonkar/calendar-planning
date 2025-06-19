from z3 import *

def main():
    # Cities mapping
    cities = ["Helsinki", "Valencia", "Dubrovnik", "Porto", "Prague", "Reykjavik"]
    # Direct flights (undirected)
    edges = [(0, 4), (4, 1), (1, 3), (0, 5), (2, 0), (5, 4)]
    allowed_edges = []
    for u, v in edges:
        allowed_edges.append((u, v))
        allowed_edges.append((v, u))
    
    # Create Z3 variables for each day (end of day)
    c = [Int('c_%d' % i) for i in range(18)]
    s = Solver()
    
    # Each day must be a valid city (0-5)
    for i in range(18):
        s.add(And(c[i] >= 0, c[i] <= 5))
    
    # Flight constraints for consecutive days
    for i in range(1, 18):
        prev = c[i-1]
        curr = c[i]
        # If the city changes, ensure there's a direct flight
        edge_ok = Or([And(prev == a, curr == b) for a, b in allowed_edges])
        s.add(Or(prev == curr, edge_ok))
    
    # Function to compute total days for a city
    def total_days(x):
        total = If(c[0] == x, 1, 0)
        for i in range(1, 18):
            total += If(Or(c[i-1] == x, c[i] == x), 1, 0)
        return total
    
    # Add constraints for each city's total days
    s.add(total_days(0) == 4)  # Helsinki
    s.add(total_days(1) == 5)  # Valencia
    s.add(total_days(2) == 4)  # Dubrovnik
    s.add(total_days(3) == 3)  # Porto
    s.add(total_days(4) == 3)  # Prague
    s.add(total_days(5) == 4)  # Reykjavik
    
    # Porto must be visited between days 16-18
    s.add(Or(
        Or(c[14] == 3, c[15] == 3),  # Day 16: indices 14 (start) and 15 (end)
        Or(c[15] == 3, c[16] == 3),   # Day 17: indices 15 (start) and 16 (end)
        Or(c[16] == 3, c[17] == 3)    # Day 18: indices 16 (start) and 17 (end)
    ))
    
    # Solve the problem
    if s.check() == sat:
        model = s.model()
        schedule = [model.evaluate(c[i]).as_long() for i in range(18)]
        # Output the schedule
        for day in range(18):
            current_city = schedule[day]
            city_name = cities[current_city]
            if day == 0:
                print(f"Day {day+1}: Stay in {city_name}")
            else:
                prev_city = schedule[day-1]
                if prev_city == current_city:
                    print(f"Day {day+1}: Stay in {city_name}")
                else:
                    prev_city_name = cities[prev_city]
                    print(f"Day {day+1}: Travel from {prev_city_name} to {city_name}, so in both {prev_city_name} and {city_name}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()