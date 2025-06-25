from z3 import *

def main():
    # Define city names and their IDs
    city_names = ["Santorini", "Krakow", "Paris", "Vilnius", "Munich", "Geneva", "Amsterdam", "Budapest", "Split"]
    city_ids = {name: idx for idx, name in enumerate(city_names)}
    
    # Required days for each city
    req_days_arr = [5, 5, 5, 3, 5, 2, 4, 5, 4]  # indexed by city ID
    
    # Define directed flight edges
    edges_list = [
        ('Paris', 'Krakow'), ('Krakow', 'Paris'),
        ('Paris', 'Amsterdam'), ('Amsterdam', 'Paris'),
        ('Paris', 'Split'), ('Split', 'Paris'),
        ('Paris', 'Geneva'), ('Geneva', 'Paris'),
        ('Amsterdam', 'Geneva'), ('Geneva', 'Amsterdam'),
        ('Munich', 'Split'), ('Split', 'Munich'),
        ('Split', 'Krakow'), ('Krakow', 'Split'),
        ('Munich', 'Amsterdam'), ('Amsterdam', 'Munich'),
        ('Budapest', 'Amsterdam'), ('Amsterdam', 'Budapest'),
        ('Split', 'Geneva'), ('Geneva', 'Split'),
        ('Vilnius', 'Split'), ('Split', 'Vilnius'),
        ('Munich', 'Geneva'), ('Geneva', 'Munich'),
        ('Munich', 'Krakow'), ('Krakow', 'Munich'),
        ('Vilnius', 'Amsterdam'), ('Amsterdam', 'Vilnius'),
        ('Budapest', 'Paris'), ('Paris', 'Budapest'),
        ('Krakow', 'Amsterdam'), ('Amsterdam', 'Krakow'),
        ('Vilnius', 'Paris'), ('Paris', 'Vilnius'),
        ('Budapest', 'Geneva'), ('Geneva', 'Budapest'),
        ('Split', 'Amsterdam'), ('Amsterdam', 'Split'),
        ('Santorini', 'Geneva'), ('Geneva', 'Santorini'),
        ('Amsterdam', 'Santorini'), ('Santorini', 'Amsterdam'),
        ('Munich', 'Budapest'), ('Budapest', 'Munich'),
        ('Munich', 'Paris'), ('Paris', 'Munich'),
        ('Vilnius', 'Munich'),
        ('Krakow', 'Vilnius')
    ]
    # Convert edges to city IDs
    edges_set = set()
    for (c1, c2) in edges_list:
        edges_set.add((city_ids[c1], city_ids[c2]))
    
    # Initialize Z3 solver
    s = Solver()
    
    # City sequence: city[0] to city[8] are the cities at positions 0 to 8
    city_vars = [Int('city_%d' % i) for i in range(9)]
    # Arrival and departure days for each position
    a_vars = [Int('a_%d' % i) for i in range(9)]
    d_vars = [Int('d_%d' % i) for i in range(9)]
    
    # Constraints
    # 1. Each city_vars[i] is between 0 and 8 (inclusive)
    for i in range(9):
        s.add(city_vars[i] >= 0, city_vars[i] <= 8)
    
    # 2. Distinct positions: all cities are visited exactly once
    s.add(Distinct(city_vars))
    
    # 3. Arrival and departure days constraints
    for i in range(9):
        # Days must be positive and within 1 to 30
        s.add(a_vars[i] >= 1, a_vars[i] <= 30)
        s.add(d_vars[i] >= 1, d_vars[i] <= 30)
        s.add(d_vars[i] >= a_vars[i])
        # The number of days in the city must match the requirement
        for cid in range(9):
            s.add(Implies(city_vars[i] == cid, d_vars[i] - a_vars[i] + 1 == req_days_arr[cid]))
    
    # 4. First city starts on day 1
    s.add(a_vars[0] == 1)
    # Last city ends on day 30
    s.add(d_vars[8] == 30)
    
    # 5. Consecutive cities: departure of current equals arrival of next
    for i in range(8):
        s.add(d_vars[i] == a_vars[i+1])
    
    # 6. Flight connections: consecutive cities must have a direct flight
    for i in range(8):
        # The pair (current city, next city) must be in edges_set
        constraints = []
        for (c1, c2) in edges_set:
            constraints.append(And(city_vars[i] == c1, city_vars[i+1] == c2))
        s.add(Or(constraints))
    
    # 7. Fixed meeting constraints
    santorini_id = city_ids['Santorini']
    krakow_id = city_ids['Krakow']
    paris_id = city_ids['Paris']
    for i in range(9):
        s.add(Implies(city_vars[i] == santorini_id, And(a_vars[i] == 25, d_vars[i] == 29)))
        s.add(Implies(city_vars[i] == krakow_id, And(a_vars[i] == 18, d_vars[i] == 22)))
        s.add(Implies(city_vars[i] == paris_id, And(a_vars[i] == 11, d_vars[i] == 15)))
    
    # Solve the problem
    if s.check() == sat:
        m = s.model()
        # Retrieve the sequence and days
        city_sequence = [m.evaluate(city_vars[i]).as_long() for i in range(9)]
        a_vals = [m.evaluate(a_vars[i]).as_long() for i in range(9)]
        d_vals = [m.evaluate(d_vars[i]).as_long() for i in range(9)]
        
        # Build itinerary list
        itinerary = []
        for i in range(9):
            cid = city_sequence[i]
            cname = city_names[cid]
            a_i = a_vals[i]
            d_i = d_vals[i]
            # Entire stay record
            if a_i == d_i:
                day_str = "Day " + str(a_i)
            else:
                day_str = "Day {}-{}".format(a_i, d_i)
            itinerary.append({"day_range": day_str, "place": cname})
            
            # If not last city, add flight day records
            if i < 8:
                # Departure from current city on d_i
                itinerary.append({"day_range": "Day " + str(d_i), "place": cname})
                # Arrival at next city on d_i (same day)
                next_cid = city_sequence[i+1]
                next_cname = city_names[next_cid]
                itinerary.append({"day_range": "Day " + str(d_i), "place": next_cname})
        
        # Output as JSON-like dictionary
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()