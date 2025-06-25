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
    
    # Create solver and variables for the first five stays (0 to 4)
    s = Solver()
    stay_city = [Int(f'c{i}') for i in range(5)]
    
    # Each stay_city must be between 0 and 4 (inclusive)
    for i in range(5):
        s.add(stay_city[i] >= 0, stay_city[i] <= 4)
    
    # All cities in the first five stays are distinct
    s.add(Distinct(stay_city))
    
    # Flight constraints between consecutive stays
    for i in range(4):
        s.add(Or([And(stay_city[i] == a, stay_city[i+1] == b) for (a, b) in allowed_pairs]))
    
    # Flight constraint from the last stay (stay5) to Nice (city5)
    s.add(Or([And(stay_city[4] == a, 5 == b) for (a, b) in allowed_pairs if b == 5]))
    
    # Oslo cannot be in stay1 or stay2 (because it would not meet the day 10-14 constraint)
    s.add(stay_city[0] != 3)
    s.add(stay_city[1] != 3)
    
    # Helper function to get required days for a city
    def get_req(city_var):
        return If(city_var == 0, 4,
                If(city_var == 1, 2,
                If(city_var == 2, 3,
                If(city_var == 3, 5, 4))))
    
    # If Oslo is in stay3, the first three cities must have at least 12 total days
    req0 = get_req(stay_city[0])
    req1 = get_req(stay_city[1])
    req2 = get_req(stay_city[2])
    total_req_first_three = req0 + req1 + req2
    s.add(If(stay_city[2] == 3, total_req_first_three >= 12, True))
    
    # Check and get model
    if s.check() == sat:
        m = s.model()
        # Get the city assignments
        assigned_cities = [m.evaluate(stay_city[i]).as_long() for i in range(5)]
        # Compute the required days for each assigned city
        reqs = [req_array[assigned_cities[i]] for i in range(5)]
        
        # Calculate start and end days for the first five stays
        s_days = [1]  # start day for stay0
        e_days = []    # end days for each stay
        for i in range(5):
            end = s_days[i] + reqs[i] - 1
            e_days.append(end)
            if i < 4:
                s_days.append(end)  # next stay starts on the same day as the current stay ends
        
        # Stay5 (Nice) starts at 14 and ends at 16
        s_days.append(14)
        e_days.append(16)
        
        # Build itinerary
        itinerary = []
        # For each stay
        for i in range(6):
            place = city_map[assigned_cities[i]] if i < 5 else "Nice"
            # Add the continuous block for the stay
            if s_days[i] == e_days[i]:
                day_range_str = f"Day {s_days[i]}"
            else:
                day_range_str = f"Day {s_days[i]}-{e_days[i]}"
            itinerary.append({"day_range": day_range_str, "place": place})
            
            # If not the last stay, add flight records
            if i < 5:
                # Departure from current city
                itinerary.append({"day_range": f"Day {e_days[i]}", "place": place})
                # Arrival at next city
                next_place = city_map[assigned_cities[i+1]] if (i+1) < 5 else "Nice"
                itinerary.append({"day_range": f"Day {e_days[i]}", "place": next_place})
        
        # Output as JSON
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == '__main__':
    main()