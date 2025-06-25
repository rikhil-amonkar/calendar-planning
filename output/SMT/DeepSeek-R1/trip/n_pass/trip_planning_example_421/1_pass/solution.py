from z3 import *
import json

def main():
    # Cities: 0=Nice, 1=Lyon, 2=Dublin, 3=Krakow, 4=Frankfurt
    names = {
        0: "Nice",
        1: "Lyon",
        2: "Dublin",
        3: "Krakow",
        4: "Frankfurt"
    }
    
    # Required days per city index
    days_req = [5, 4, 7, 6, 2]
    
    # Graph: list of directed edges (for undirected, we have both ways)
    edges = [
        (0,2), (2,0),
        (2,4), (4,2),
        (2,3), (3,2),
        (3,4), (4,3),
        (1,4), (4,1),
        (0,4), (4,0),
        (1,2), (2,1),
        (0,1), (1,0)
    ]
    
    # Create Z3 variables
    p1, p2, p3 = Ints('p1 p2 p3')
    
    s = Solver()
    
    # Constraints: p1, p2, p3 are distinct and in {1,2,3}
    s.add(Distinct(p1, p2, p3))
    s.add(And(p1 >= 1, p1 <= 3))
    s.add(And(p2 >= 1, p2 <= 3))
    s.add(And(p3 >= 1, p3 <= 3))
    
    # Define a function to check edge
    def has_edge(a, b):
        return Or([And(a == i, b == j) for (i, j) in edges])
    
    # Constraints for the flights
    s.add(has_edge(0, p1))   # from Nice to first city
    s.add(has_edge(p1, p2))  # from first to second
    s.add(has_edge(p2, p3))  # from second to third
    s.add(has_edge(p3, 4))   # from third to Frankfurt
    
    if s.check() == sat:
        m = s.model()
        p1_val = m[p1].as_long()
        p2_val = m[p2].as_long()
        p3_val = m[p3].as_long()
        
        # Build the order: [0, p1_val, p2_val, p3_val, 4]
        order = [0, p1_val, p2_val, p3_val, 4]
        
        # Now compute the start and end days for each city in the order
        start = [0] * 5
        end = [0] * 5
        
        # First city: Nice
        start[0] = 1
        end[0] = start[0] + days_req[order[0]] - 1   # 1+5-1 = 5
        
        for i in range(1, 5):
            start[i] = end[i-1]
            end[i] = start[i] + days_req[order[i]] - 1
        
        # Now, build the itinerary list
        itinerary_list = []
        
        for i in range(5):
            city_index = order[i]
            city_name = names[city_index]
            
            # The block for the entire stay in this city
            block_record = {
                "day_range": f"Day {start[i]}-{end[i]}",
                "place": city_name
            }
            itinerary_list.append(block_record)
            
            # If this is not the last city, then we have a flight to the next city on the end day of this city
            if i < 4:
                # Departure record for the current city
                dep_record = {
                    "day_range": f"Day {end[i]}",
                    "place": city_name
                }
                # Arrival record for the next city
                next_city_index = order[i+1]
                next_city_name = names[next_city_index]
                arr_record = {
                    "day_range": f"Day {end[i]}",
                    "place": next_city_name
                }
                itinerary_list.append(dep_record)
                itinerary_list.append(arr_record)
        
        # Create the result dictionary
        result = {
            "itinerary": itinerary_list
        }
        
        # Output as JSON string
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()