from z3 import *

def main():
    # Define the directed flight edges
    edges = [
        (1, 2), (2, 1), (3, 4), (4, 3), (0, 4), (4, 0), 
        (2, 3), (3, 2), (5, 1), (1, 5), (5, 4), (4, 5), 
        (0, 1), (1, 0), (5, 0), (0, 5), (4, 6), (6, 4), 
        (5, 3), (3, 5), (1, 4), (4, 1), (2, 4), (5, 2)
    ]
    
    # Cities: 0=Mykonos, 1=Nice, 2=Riga, 3=Bucharest, 4=Munich, 5=Rome, 6=Krakow
    city_map = {
        0: "Mykonos",
        1: "Nice",
        2: "Riga",
        3: "Bucharest",
        4: "Munich",
        5: "Rome",
        6: "Krakow"
    }
    
    # Durations for cities 0,1,2,3: [Mykonos, Nice, Riga, Bucharest] -> [3,3,3,4]
    dur_list = [3, 3, 3, 4]
    
    # Define variables for the permutation of intermediate cities (positions 1 to 4)
    p0, p1, p2, p3 = Ints('p0 p1 p2 p3')
    s = Solver()
    
    # Each variable must be in [0,3] and distinct
    s.add(Distinct(p0, p1, p2, p3))
    for x in [p0, p1, p2, p3]:
        s.add(x >= 0, x <= 3)
    
    # Mykonos (0) must be at position0 or position1; if at position1, then p0 cannot be 3 (Bucharest) because that would make the start day of Mykonos too late.
    s.add(Or(p0 == 0, p1 == 0))
    s.add(Implies(p1 == 0, p0 != 3))
    
    # Helper function to check if (a, b) is in the edges
    def in_edges(a, b, edges_list):
        options = []
        for (x, y) in edges_list:
            options.append(And(a == x, b == y))
        return Or(options)
    
    # Flight connections between consecutive cities in the sequence
    s.add(in_edges(p0, p1, edges))
    s.add(in_edges(p1, p2, edges))
    s.add(in_edges(p2, p3, edges))
    
    # Solve
    if s.check() == sat:
        m = s.model()
        p0_val = m[p0].as_long()
        p1_val = m[p1].as_long()
        p2_val = m[p2].as_long()
        p3_val = m[p3].as_long()
        
        # Durations for the intermediate cities
        d0 = dur_list[p0_val]
        d1 = dur_list[p1_val]
        d2 = dur_list[p2_val]
        d3 = dur_list[p3_val]
        
        # Start and end days for each city in the sequence
        # The sequence: [Rome, city1, city2, city3, city4, Munich, Krakow]
        cities = [5, p0_val, p1_val, p2_val, p3_val, 4, 6]
        # Start days: 
        s_vals = [
            1,  # Rome starts at day1
            4,  # city1 starts at day4 (since Rome ends at day4)
            3 + d0,  # city2 starts at 3 + d0
            2 + d0 + d1,  # city3 starts at 2 + d0 + d1
            1 + d0 + d1 + d2,  # city4 starts at 1 + d0 + d1 + d2
            d0 + d1 + d2 + d3,  # Munich starts at d0+d1+d2+d3 (since city4 ends at that day)
            16  # Krakow starts at day16
        ]
        # End days: 
        e_vals = [
            4,  # Rome ends at day4
            3 + d0,  # city1 ends at 3 + d0 (start + d0 - 1 = 4 + d0 - 1 = 3+d0)
            2 + d0 + d1,  # city2 ends at 2 + d0 + d1
            1 + d0 + d1 + d2,  # city3 ends at 1 + d0 + d1 + d2
            d0 + d1 + d2 + d3,  # city4 ends at d0+d1+d2+d3
            d0 + d1 + d2 + d3 + 3,  # Munich: 4 days -> ends at start+4-1 = s5+3
            17  # Krakow ends at day17
        ]
        
        # Build the itinerary
        itinerary = []
        for i in range(7):
            city_name = city_map[cities[i]]
            s_i = s_vals[i]
            e_i = e_vals[i]
            
            # Format the entire stay block
            if s_i == e_i:
                day_str = f"Day {s_i}"
            else:
                day_str = f"Day {s_i}-{e_i}"
            itinerary.append({"day_range": day_str, "place": city_name})
            
            # If not the last city, add departure and arrival for the flight day
            if i < 6:
                # Departure from current city on day e_i
                itinerary.append({"day_range": f"Day {e_i}", "place": city_name})
                # Arrival at next city on day e_i (which is the same as the next city's start day)
                next_city_name = city_map[cities[i+1]]
                itinerary.append({"day_range": f"Day {e_i}", "place": next_city_name})
        
        # Output the itinerary in JSON format
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()