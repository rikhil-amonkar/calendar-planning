from z3 import *

def main():
    s = Solver()
    e0 = Int('e0')
    e1 = Int('e1')
    e2 = Int('e2')
    
    s.add(e0 >= 1, e0 <= 12)
    s.add(e1 >= e0, e1 <= 12)
    s.add(e2 >= e1, e2 <= 12)
    
    days0 = e0
    days1 = e1 - e0 + 1
    days2 = e2 - e1 + 1
    days3 = 13 - e2
    
    s.add(days0 == 4)
    s.add(days1 == 4)
    s.add(days2 == 4)
    s.add(days3 == 3)
    
    city0 = Int('city0')
    city1 = Int('city1')
    city2 = Int('city2')
    city3 = 3
    
    s.add(city0 >= 0, city0 <= 2)
    s.add(city1 >= 0, city1 <= 2)
    s.add(city2 >= 0, city2 <= 2)
    s.add(Distinct(city0, city1, city2, city3))
    
    allowed_pairs = [
        (0, 1), (1, 0),
        (0, 0), (1, 1), (2, 2), (3, 3),
        (1, 2), (2, 1),
        (1, 3), (3, 1),
        (2, 3), (3, 2)
    ]
    
    edge0_ok = Or([And(city0 == i, city1 == j) for (i, j) in allowed_pairs])
    edge1_ok = Or([And(city1 == i, city2 == j) for (i, j) in allowed_pairs])
    edge2_ok = Or([And(city2 == i, city3 == j) for (i, j) in allowed_pairs])
    
    s.add(edge0_ok, edge1_ok, edge2_ok)
    
    if s.check() == sat:
        m = s.model()
        e0_val = m[e0].as_long()
        e1_val = m[e1].as_long()
        e2_val = m[e2].as_long()
        city0_val = m[city0].as_long()
        city1_val = m[city1].as_long()
        city2_val = m[city2].as_long()
        
        cities = ["Valencia", "Naples", "Manchester", "Oslo"]
        city_names = {
            0: "Valencia",
            1: "Naples",
            2: "Manchester",
            3: "Oslo"
        }
        
        c0 = city_names[city0_val]
        c1 = city_names[city1_val]
        c2 = city_names[city2_val]
        c3 = "Oslo"
        
        itinerary = []
        itinerary.append({"day_range": "Day 1-{}".format(e0_val), "place": c0})
        itinerary.append({"day_range": "Day {}".format(e0_val), "place": c0})
        itinerary.append({"day_range": "Day {}".format(e0_val), "place": c1})
        itinerary.append({"day_range": "Day {}-{}".format(e0_val, e1_val), "place": c1})
        itinerary.append({"day_range": "Day {}".format(e1_val), "place": c1})
        itinerary.append({"day_range": "Day {}".format(e1_val), "place": c2})
        itinerary.append({"day_range": "Day {}-{}".format(e1_val, e2_val), "place": c2})
        itinerary.append({"day_range": "Day {}".format(e2_val), "place": c2})
        itinerary.append({"day_range": "Day {}".format(e2_val), "place": c3})
        itinerary.append({"day_range": "Day {}-12".format(e2_val), "place": c3})
        itinerary.append({"day_range": "Day 12", "place": c3})
        itinerary.append({"day_range": "Day 12", "place": "Vilnius"})
        itinerary.append({"day_range": "Day 12-13", "place": "Vilnius"})
        itinerary.append({"day_range": "Day 13", "place": "Vilnius"})
        itinerary.append({"day_range": "Day 13", "place": "Frankfurt"})
        itinerary.append({"day_range": "Day 13-16", "place": "Frankfurt"})
        
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == '__main__':
    main()