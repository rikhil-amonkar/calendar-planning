from z3 import *

def main():
    cities = ["Brussels", "Helsinki", "Split", "Dubrovnik", "Milan"]
    days_req = [3, 3, 4, 2, 4]
    graph = {
        0: [1, 4],
        1: [0, 2, 3, 4],
        2: [1, 4],
        3: [1],
        4: [0, 1, 2]
    }
    allowed_set = set()
    for i in range(5):
        for j in graph[i]:
            allowed_set.add((i, j))
    
    c0, c1, c2, c3, c4 = Ints('c0 c1 c2 c3 c4')
    s = Solver()
    s.add(c0 >= 0, c0 < 5, c1 >= 0, c1 < 5, c2 >= 0, c2 < 5, c3 >= 0, c3 < 5, c4 >= 0, c4 < 5)
    s.add(Distinct(c0, c1, c2, c3, c4))
    s.add(Or(c0 == 0, c0 == 1, c0 == 4))
    
    # Constraints for consecutive edges
    s.add(Or([And(c0 == i, c1 == j) for (i, j) in allowed_set]))
    s.add(Or([And(c1 == i, c2 == j) for (i, j) in allowed_set]))
    s.add(Or([And(c2 == i, c3 == j) for (i, j) in allowed_set]))
    s.add(Or([And(c3 == i, c4 == j) for (i, j) in allowed_set]))
    
    if s.check() == sat:
        m = s.model()
        c0_val = m[c0].as_long()
        c1_val = m[c1].as_long()
        c2_val = m[c2].as_long()
        c3_val = m[c3].as_long()
        c4_val = m[c4].as_long()
        
        d0 = days_req[c0_val]
        d1 = days_req[c1_val]
        d2 = days_req[c2_val]
        d3 = days_req[c3_val]
        d4 = days_req[c4_val]
        
        a0 = d0 + 4
        a1 = d0 + d1 + 3
        a2 = d0 + d1 + d2 + 2
        a3 = d0 + d1 + d2 + d3 + 1
        
        itinerary = []
        itinerary.append({"day_range": "Day 1-5", "place": "Istanbul"})
        itinerary.append({"day_range": "Day 5", "place": "Istanbul"})
        
        city0 = cities[c0_val]
        itinerary.append({"day_range": "Day 5", "place": city0})
        itinerary.append({"day_range": f"Day 5-{a0}", "place": city0})
        itinerary.append({"day_range": f"Day {a0}", "place": city0})
        
        city1 = cities[c1_val]
        itinerary.append({"day_range": f"Day {a0}", "place": city1})
        itinerary.append({"day_range": f"Day {a0}-{a1}", "place": city1})
        itinerary.append({"day_range": f"Day {a1}", "place": city1})
        
        city2 = cities[c2_val]
        itinerary.append({"day_range": f"Day {a1}", "place": city2})
        itinerary.append({"day_range": f"Day {a1}-{a2}", "place": city2})
        itinerary.append({"day_range": f"Day {a2}", "place": city2})
        
        city3 = cities[c3_val]
        itinerary.append({"day_range": f"Day {a2}", "place": city3})
        itinerary.append({"day_range": f"Day {a2}-{a3}", "place": city3})
        itinerary.append({"day_range": f"Day {a3}", "place": city3})
        
        city4 = cities[c4_val]
        itinerary.append({"day_range": f"Day {a3}", "place": city4})
        itinerary.append({"day_range": f"Day {a3}-16", "place": city4})
        itinerary.append({"day_range": "Day 16", "place": city4})
        
        itinerary.append({"day_range": "Day 16", "place": "Frankfurt"})
        itinerary.append({"day_range": "Day 16-18", "place": "Frankfurt"})
        itinerary.append({"day_range": "Day 18", "place": "Frankfurt"})
        
        itinerary.append({"day_range": "Day 18", "place": "Vilnius"})
        itinerary.append({"day_range": "Day 18-22", "place": "Vilnius"})
        
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()