from z3 import *

def main():
    # City mapping: 0=Mykonos, 1=London, 2=Copenhagen, 3=Oslo, 4=Tallinn, 5=Nice
    city_map = {
        0: "Mykonos",
        1: "London",
        2: "Copenhagen",
        3: "Oslo",
        4: "Tallinn",
        5: "Nice"
    }
    
    # Required days for cities 0 to 4 (Mykonos, London, Copenhagen, Oslo, Tallinn)
    req_array = [4, 2, 3, 5, 4]
    
    # Flight connections (undirected graph represented as directed edges both ways)
    flights = [
        (0, 1), (1, 0),  # Mykonos <-> London
        (0, 5), (5, 0),  # Mykonos <-> Nice
        (1, 2), (2, 1),  # London <-> Copenhagen
        (1, 3), (3, 1),  # London <-> Oslo
        (1, 5), (5, 1),  # London <-> Nice
        (2, 4), (4, 2),  # Copenhagen <-> Tallinn
        (2, 3), (3, 2),  # Copenhagen <-> Oslo
        (2, 5), (5, 2),  # Copenhagen <-> Nice
        (3, 4), (4, 3),  # Oslo <-> Tallinn
        (3, 5), (5, 3)   # Oslo <-> Nice
    ]
    allowed_pairs = set(flights)
    
    # Create solver and variables for the five non-Nice stays
    s = Solver()
    stay_city = [Int(f'c{i}') for i in range(5)]
    
    # The fifth stay must be Oslo (index 3)
    s.add(stay_city[4] == 3)
    
    # For the first four stays, they must be from {0,1,2,4} (Mykonos, London, Copenhagen, Tallinn)
    for i in range(4):
        s.add(Or(stay_city[i] == 0, stay_city[i] == 1, stay_city[i] == 2, stay_city[i] == 4))
    
    # All five non-Nice stays must be distinct
    s.add(Distinct(stay_city))
    
    # Helper function to get required days for a city index in [0,4]
    def get_req(city_var):
        return If(city_var == 0, 4,
                If(city_var == 1, 2,
                If(city_var == 2, 3,
                If(city_var == 3, 5, 4))))
    
    # Sum of days for the first four stays must be 13
    req0 = get_req(stay_city[0])
    req1 = get_req(stay_city[1])
    req2 = get_req(stay_city[2])
    req3 = get_req(stay_city[3])
    s.add(req0 + req1 + req2 + req3 == 13)
    
    # Flight constraints between consecutive stays
    for i in range(4):
        city_i = stay_city[i]
        city_j = stay_city[i+1]
        s.add(Or([And(city_i == a, city_j == b) for (a, b) in allowed_pairs]))
    
    # Flight constraint from the fifth stay (Oslo) to Nice
    s.add(Or([And(stay_city[4] == a, 5 == b) for (a, b) in allowed_pairs if b == 5]))
    
    # Check and get model
    if s.check() == sat:
        m = s.model()
        assigned_cities = [m.evaluate(stay_city[i]).as_long() for i in range(5)]
        reqs = [req_array[assigned_cities[i]] for i in range(5)]
        
        # Compute start and end days for the five non-Nice stays
        starts = [1]
        ends = []
        for i in range(5):
            end_i = starts[i] + reqs[i] - 1
            ends.append(end_i)
            if i < 4:
                starts.append(end_i)  # next stay starts on the same day the current stay ends
        
        # Add Nice as the sixth stay: starts at the end of the fifth stay (Oslo) and lasts 3 days
        starts.append(ends[4])  # start of Nice
        ends.append(starts[5] + 2)  # end of Nice: 3 days -> starts[5] to starts[5]+2
        
        # Build the itinerary
        itinerary = []
        for i in range(6):
            if i < 5:
                place = city_map[assigned_cities[i]]
            else:
                place = "Nice"
            
            # Continuous block for the stay
            start = starts[i]
            end = ends[i]
            if start == end:
                day_range_str = f"Day {start}"
            else:
                day_range_str = f"Day {start}-{end}"
            itinerary.append({"day_range": day_range_str, "place": place})
            
            # If not the last stay, add departure and arrival records for the flight day
            if i < 5:
                # Departure from current city on the end day
                itinerary.append({"day_range": f"Day {end}", "place": place})
                # Arrival at next city on the same day
                next_place = city_map[assigned_cities[i+1]] if i < 4 else "Nice"
                itinerary.append({"day_range": f"Day {end}", "place": next_place})
        
        # Output as JSON
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == '__main__':
    main()