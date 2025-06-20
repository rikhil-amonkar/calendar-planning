from z3 import *

def main():
    days_dict = {
        'Krakow': 5,
        'Frankfurt': 4,
        'Dubrovnik': 5,
        'Naples': 5,
        'Oslo': 3
    }
    
    cities = ['Krakow', 'Frankfurt', 'Dubrovnik', 'Naples']
    city_to_int = {city: idx for idx, city in enumerate(cities)}
    
    c1, c2, c3, c4 = Ints('c1 c2 c3 c4')
    s = Solver()
    
    s.add(c1 >= 0, c1 <= 3)
    s.add(c2 >= 0, c2 <= 3)
    s.add(c3 >= 0, c3 <= 3)
    s.add(c4 >= 0, c4 <= 3)
    s.add(Distinct(c1, c2, c3, c4))
    
    def adjacent(i, j):
        return Or(
            And(i == 0, j == 1),
            And(i == 1, Or(j == 0, j == 2, j == 3)),
            And(i == 2, Or(j == 1, j == 3)),
            And(i == 3, Or(j == 1, j == 2))
        )
    
    s.add(adjacent(c1, c2))
    s.add(adjacent(c2, c3))
    s.add(adjacent(c3, c4))
    
    if s.check() == sat:
        m = s.model()
        c1_val = m[c1].as_long()
        c2_val = m[c2].as_long()
        c3_val = m[c3].as_long()
        c4_val = m[c4].as_long()
        
        c1_name = cities[c1_val]
        c2_name = cities[c2_val]
        c3_name = cities[c3_val]
        c4_name = cities[c4_val]
        
        s1 = 1
        e1 = s1 + days_dict[c1_name] - 1
        
        s2 = e1
        e2 = s2 + days_dict[c2_name] - 1
        
        s3 = e2
        e3 = s3 + days_dict[c3_name] - 1
        
        s4 = e3
        e4 = s4 + days_dict[c4_name] - 1
        
        s5 = 16
        e5 = 18
        
        itinerary = []
        
        itinerary.append({"day_range": f"Day {s1}-{e1}", "place": c1_name})
        itinerary.append({"day_range": f"Day {e1}", "place": c1_name})
        itinerary.append({"day_range": f"Day {e1}", "place": c2_name})
        
        itinerary.append({"day_range": f"Day {s2}-{e2}", "place": c2_name})
        itinerary.append({"day_range": f"Day {e2}", "place": c2_name})
        itinerary.append({"day_range": f"Day {e2}", "place": c3_name})
        
        itinerary.append({"day_range": f"Day {s3}-{e3}", "place": c3_name})
        itinerary.append({"day_range": f"Day {e3}", "place": c3_name})
        itinerary.append({"day_range": f"Day {e3}", "place": c4_name})
        
        itinerary.append({"day_range": f"Day {s4}-{e4}", "place": c4_name})
        itinerary.append({"day_range": f"Day {e4}", "place": c4_name})
        itinerary.append({"day_range": f"Day {e4}", "place": "Oslo"})
        
        itinerary.append({"day_range": f"Day {s5}-{e5}", "place": "Oslo"})
        
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()