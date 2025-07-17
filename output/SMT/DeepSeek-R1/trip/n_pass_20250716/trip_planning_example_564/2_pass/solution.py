from z3 import *

def main():
    # Cities: 0: Seville, 1: Rome, 2: Istanbul, 3: Naples, 4: Santorini
    city_names = {
        0: "Seville",
        1: "Rome",
        2: "Istanbul",
        3: "Naples",
        4: "Santorini"
    }
    
    # Define variables for the city sequence
    c0, c1, c2, c3, c4 = Ints('c0 c1 c2 c3 c4')
    # Variables for end days of the first four segments (e0, e1, e2, e3)
    e0, e1, e2, e3 = Ints('e0 e1 e2 e3')
    
    s = Solver()
    
    # Constraint: cities are between 0 and 4, distinct, and c4 is Santorini (4)
    s.add(c0 >= 0, c0 <= 4)
    s.add(c1 >= 0, c1 <= 4)
    s.add(c2 >= 0, c2 <= 4)
    s.add(c3 >= 0, c3 <= 4)
    s.add(c4 == 4)
    s.add(Distinct(c0, c1, c2, c3, c4))
    
    # Start and end day constraints
    s.add(e0 >= 1, e1 >= e0, e2 >= e1, e3 >= e2)
    s.add(e3 == 13)  # because the next segment (Santorini) starts at day 13
    
    # Stay duration constraints for each segment using nested If expressions
    s.add(e0 == If(c0 == 0, 4,
               If(c0 == 1, 3,
               If(c0 == 2, 2,
               If(c0 == 3, 7, 4)))))
    
    s.add(e1 - e0 + 1 == If(c1 == 0, 4,
                        If(c1 == 1, 3,
                        If(c1 == 2, 2,
                        If(c1 == 3, 7, 4)))))
    
    s.add(e2 - e1 + 1 == If(c2 == 0, 4,
                        If(c2 == 1, 3,
                        If(c2 == 2, 2,
                        If(c2 == 3, 7, 4)))))
    
    s.add(14 - e2 == If(c3 == 0, 4,
                   If(c3 == 1, 3,
                   If(c3 == 2, 2,
                   If(c3 == 3, 7, 4)))))
    
    # Fixed events: Istanbul must be on days 6 and 7
    s.add(Or(
        And(c1 == 2, e0 == 6, e1 == 7),
        And(c2 == 2, e1 == 6, e2 == 7)
    ))
    
    # Flight connections: define allowed edges (undirected)
    def connected(i, j):
        return Or(
            And(i == 0, j == 1),
            And(i == 1, j == 0),
            And(i == 1, j == 4),
            And(i == 4, j == 1),
            And(i == 2, j == 3),
            And(i == 3, j == 2),
            And(i == 3, j == 4),
            And(i == 4, j == 3),
            And(i == 1, j == 3),
            And(i == 3, j == 1),
            And(i == 1, j == 2),
            And(i == 2, j == 1)
        )
    
    s.add(connected(c0, c1))
    s.add(connected(c1, c2))
    s.add(connected(c2, c3))
    s.add(connected(c3, c4))
    
    # Check and get model
    if s.check() == sat:
        m = s.model()
        c0_val = m[c0].as_long()
        c1_val = m[c1].as_long()
        c2_val = m[c2].as_long()
        c3_val = m[c3].as_long()
        e0_val = m[e0].as_long()
        e1_val = m[e1].as_long()
        e2_val = m[e2].as_long()
        
        # Santorini is fixed as the last city
        cities = [c0_val, c1_val, c2_val, c3_val, 4]
        starts = [1, e0_val, e1_val, e2_val, 13]
        ends = [e0_val, e1_val, e2_val, 13, 16]
        
        itinerary = []
        for i in range(5):
            city_idx = cities[i]
            city_name = city_names[city_idx]
            s_day = starts[i]
            e_day = ends[i]
            
            # Entire stay in the city
            itinerary.append({
                "day_range": f"Day {s_day}-{e_day}",
                "place": city_name
            })
            
            # If not the last city, add flight day records
            if i < 4:
                # Departure from current city
                itinerary.append({
                    "day_range": f"Day {e_day}",
                    "place": city_name
                })
                # Arrival in next city
                next_city_name = city_names[cities[i+1]]
                itinerary.append({
                    "day_range": f"Day {e_day}",
                    "place": next_city_name
                })
        
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()