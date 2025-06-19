from z3 import *
import json

def main():
    # Define the city indices
    cities = ['Manchester', 'Istanbul', 'Venice', 'Krakow', 'Lyon']
    n_cities = len(cities)
    
    # Allowed directed flight edges (both directions for undirected graph)
    allowed_edges = [
        (0, 1), (1, 0),  # Manchester - Istanbul
        (0, 2), (2, 0),  # Manchester - Venice
        (0, 3), (3, 0),  # Manchester - Krakow
        (1, 2), (2, 1),  # Istanbul - Venice
        (1, 3), (3, 1),  # Istanbul - Krakow
        (1, 4), (4, 1),  # Istanbul - Lyon
        (2, 4), (4, 2)   # Venice - Lyon
    ]
    
    # Create Z3 variables for the city sequence and end days
    c0, c1, c2, c3, c4 = Ints('c0 c1 c2 c3 c4')
    e1, e2, e3, e4 = Ints('e1 e2 e3 e4')
    
    s = Solver()
    
    # Each city variable must be between 0 and 4 (inclusive)
    s.add(c0 >= 0, c0 < n_cities)
    s.add(c1 >= 0, c1 < n_cities)
    s.add(c2 >= 0, c2 < n_cities)
    s.add(c3 >= 0, c3 < n_cities)
    s.add(c4 >= 0, c4 < n_cities)
    s.add(Distinct(c0, c1, c2, c3, c4))
    
    # End day constraints: 1 <= e1 <= e2 <= e3 <= e4 <= 21
    s.add(e1 >= 1, e1 <= 21)
    s.add(e2 >= e1, e2 <= 21)
    s.add(e3 >= e2, e3 <= 21)
    s.add(e4 >= e3, e4 <= 21)
    
    # Flight constraints: consecutive cities must have a direct flight
    def flight_ok(i, j):
        return Or([And(i == u, j == v) for (u, v) in allowed_edges])
    
    s.add(flight_ok(c0, c1))
    s.add(flight_ok(c1, c2))
    s.add(flight_ok(c2, c3))
    s.add(flight_ok(c3, c4))
    
    # Days spent in each segment
    days0 = e1
    days1 = e2 - e1 + 1
    days2 = e3 - e2 + 1
    days3 = e4 - e3 + 1
    days4 = 21 - e4 + 1
    
    # Constraints for each city's total days
    man_days = If(c0 == 0, days0,
              If(c1 == 0, days1,
              If(c2 == 0, days2,
              If(c3 == 0, days3,
              If(c4 == 0, days4, 0)))))
    s.add(man_days == 3)
    
    ist_days = If(c0 == 1, days0,
              If(c1 == 1, days1,
              If(c2 == 1, days2,
              If(c3 == 1, days3,
              If(c4 == 1, days4, 0)))))
    s.add(ist_days == 7)
    
    ven_days = If(c0 == 2, days0,
              If(c1 == 2, days1,
              If(c2 == 2, days2,
              If(c3 == 2, days3,
              If(c4 == 2, days4, 0)))))
    s.add(ven_days == 7)
    
    kra_days = If(c0 == 3, days0,
              If(c1 == 3, days1,
              If(c2 == 3, days2,
              If(c3 == 3, days3,
              If(c4 == 3, days4, 0)))))
    s.add(kra_days == 6)
    
    lyo_days = If(c0 == 4, days0,
              If(c1 == 4, days1,
              If(c2 == 4, days2,
              If(c3 == 4, days3,
              If(c4 == 4, days4, 0)))))
    s.add(lyo_days == 2)
    
    # Event constraints
    man_pos = If(c0 == 0, 0,
             If(c1 == 0, 1,
             If(c2 == 0, 2,
             If(c3 == 0, 3,
             If(c4 == 0, 4, -1)))))
    s.add(If(man_pos == 0, True,
          If(man_pos == 1, e1 <= 3,
          If(man_pos == 2, e2 <= 3,
          If(man_pos == 3, e3 <= 3,
          If(man_pos == 4, e4 <= 3, False))))))
    
    ven_pos = If(c0 == 2, 0,
             If(c1 == 2, 1,
             If(c2 == 2, 2,
             If(c3 == 2, 3,
             If(c4 == 2, 4, -1)))))
    s.add(If(ven_pos == 0, e1 >= 3,
          If(ven_pos == 1, And(e1 <= 9, e2 >= 3),
          If(ven_pos == 2, And(e2 <= 9, e3 >= 3),
          If(ven_pos == 3, And(e3 <= 9, e4 >= 3),
          If(ven_pos == 4, e4 <= 9, False)))))
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        c0_val = m[c0].as_long()
        c1_val = m[c1].as_long()
        c2_val = m[c2].as_long()
        c3_val = m[c3].as_long()
        c4_val = m[c4].as_long()
        e1_val = m[e1].as_long()
        e2_val = m[e2].as_long()
        e3_val = m[e3].as_long()
        e4_val = m[e4].as_long()
        
        city0 = cities[c0_val]
        city1 = cities[c1_val]
        city2 = cities[c2_val]
        city3 = cities[c3_val]
        city4 = cities[c4_val]
        
        itinerary_list = []
        
        # First stay: city0 from day 1 to e1_val
        itinerary_list.append({"day_range": "Day 1-{}".format(e1_val), "place": city0})
        itinerary_list.append({"day_range": "Day {}".format(e1_val), "place": city0})
        itinerary_list.append({"day_range": "Day {}".format(e1_val), "place": city1})
        
        # Second stay: city1 from e1_val to e2_val
        itinerary_list.append({"day_range": "Day {}-{}".format(e1_val, e2_val), "place": city1})
        itinerary_list.append({"day_range": "Day {}".format(e2_val), "place": city1})
        itinerary_list.append({"day_range": "Day {}".format(e2_val), "place": city2})
        
        # Third stay: city2 from e2_val to e3_val
        itinerary_list.append({"day_range": "Day {}-{}".format(e2_val, e3_val), "place": city2})
        itinerary_list.append({"day_range": "Day {}".format(e3_val), "place": city2})
        itinerary_list.append({"day_range": "Day {}".format(e3_val), "place": city3})
        
        # Fourth stay: city3 from e3_val to e4_val
        itinerary_list.append({"day_range": "Day {}-{}".format(e3_val, e4_val), "place": city3})
        itinerary_list.append({"day_range": "Day {}".format(e4_val), "place": city3})
        itinerary_list.append({"day_range": "Day {}".format(e4_val), "place": city4})
        
        # Fifth stay: city4 from e4_val to 21
        itinerary_list.append({"day_range": "Day {}-21".format(e4_val), "place": city4})
        
        result = {"itinerary": itinerary_list}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()