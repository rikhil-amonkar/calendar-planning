from z3 import *

def main():
    # City indices
    cities = ["Paris", "Amsterdam", "Hamburg", "Warsaw", "Vilnius", "Tallinn", "Barcelona", "Florence", "Venice", "Salzburg"]
    n_cities = len(cities)
    n_stays = 11
    n_travel_days = 10
    total_days = 24
    total_stay_days = total_days - n_travel_days  # 14

    # Create city variables for 11 stays
    c = [Int('c_%d' % i) for i in range(n_stays)]
    # Create duration variables for 11 stays
    d = [Int('d_%d' % i) for i in range(n_stays)]
    
    s = Solver()
    
    # City constraints: c0 and c10 must be Paris (0)
    s.add(c[0] == 0)
    s.add(c[10] == 0)
    
    # Durations: each between 1 and 5, and sum to 14
    for i in range(n_stays):
        s.add(d[i] >= 1)
        s.add(d[i] <= 5)
    s.add(sum(d) == total_stay_days)
    
    # The inner 9 cities (c1 to c9) must be a permutation of the other 9 cities (1 to 9)
    s.add(Distinct([c[i] for i in range(1, 10)]))
    for i in range(1, 10):
        s.add(c[i] >= 1, c[i] <= 9)
    
    # Define allowed edges (bidirectional)
    edges = [
        (0, 1), (0, 6),  # Paris connections
        (1, 2),           # Amsterdam - Hamburg
        (2, 3),           # Hamburg - Warsaw
        (3, 4), (3, 8),   # Warsaw connections
        (4, 5),           # Vilnius - Tallinn
        (7, 8),           # Florence - Venice
        (8, 9)            # Venice - Salzburg
    ]
    # Make bidirectional
    allowed_edges = []
    for u, v in edges:
        allowed_edges.append((u, v))
        allowed_edges.append((v, u))
    
    # Constraint: consecutive cities in the sequence must be connected by an edge
    for i in range(n_stays - 1):
        edge_constraints = []
        for u, v in allowed_edges:
            edge_constraints.append(And(c[i] == u, c[i+1] == v))
        s.add(Or(edge_constraints))
    
    # Check and get model
    if s.check() == sat:
        model = s.model()
        city_vals = [model.evaluate(c[i]).as_long() for i in range(n_stays)]
        dur_vals = [model.evaluate(d[i]).as_long() for i in range(n_stays)]
        
        # Print the plan
        current_day = 1
        itinerary = []
        for i in range(n_stays):
            start_day = current_day
            end_day = current_day + dur_vals[i] - 1
            if start_day == end_day:
                day_range = f"Day {start_day}"
            else:
                day_range = f"Day {start_day}-{end_day}"
            itinerary.append({'day_range': day_range, 'place': cities[city_vals[i]]})
            current_day = end_day + 1  # next day is travel day
            if i < n_stays - 1:
                current_day += 1  # add the travel day (already counted in the next stay's start)
        # Note: The travel days are accounted for between stays, so the next stay starts after the travel day.
        
        plan = {'itinerary': itinerary}
        print("Plan found:", plan)
    else:
        print("No valid plan found")

if __name__ == "__main__":
    main()