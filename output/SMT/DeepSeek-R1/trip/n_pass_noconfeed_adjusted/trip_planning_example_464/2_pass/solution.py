from z3 import *

def main():
    # Cities: Naples=0, Krakow=1, Frankfurt=2, Dubrovnik=3, Oslo=4
    cities = ["Naples", "Krakow", "Frankfurt", "Dubrovnik", "Oslo"]
    required_days = [5, 5, 4, 5, 3]
    
    # Direct flights (symmetric)
    flights = [(3,4), (2,1), (2,4), (3,2), (1,4), (0,4), (0,3), (0,2)]
    
    s = Solver()
    
    # Order of cities (permutation)
    order = [Int(f"order_{i}") for i in range(5)]
    for i in range(5):
        s.add(And(order[i] >= 0, order[i] <= 4))
    s.add(Distinct(order))
    s.add(order[4] == 4)  # Oslo is last
    
    # Start days for each city's full stay
    start = [Int(f"start_{i}") for i in range(5)]
    # Duration of full days for each city
    S = [Int(f"S_{i}") for i in range(5)]
    
    # Function to get required days using Z3 expressions
    def get_req_days(idx):
        return If(idx == 0, required_days[0],
               If(idx == 1, required_days[1],
               If(idx == 2, required_days[2],
               If(idx == 3, required_days[3], required_days[4]))))
    
    # Constraints for first city
    s.add(start[0] == 1)
    s.add(get_req_days(order[0]) == S[0] + 1)
    
    # Constraints for middle cities
    for i in range(1, 4):
        s.add(get_req_days(order[i]) == S[i] + 2)
        s.add(start[i] == start[i-1] + S[i-1] + 1)
    
    # Constraints for last city
    s.add(get_req_days(order[4]) == S[4] + 1)
    s.add(start[4] == start[3] + S[3] + 1)
    s.add(start[4] + S[4] - 1 == 18)  # Last day is 18
    
    # Dubrovnik must cover days 5-9
    for i in range(5):
        # Check if city i is Dubrovnik
        condition = And(start[i] <= 5, start[i] + S[i] - 1 >= 9)
        s.add(If(order[i] == 3, condition, True))
    
    # Flight connections between consecutive cities
    for i in range(4):
        city_i = order[i]
        city_j = order[i+1]
        # Check if there is a direct flight between city_i and city_j
        flight_exists = Or(
            *[Or(And(city_i == a, city_j == b), And(city_i == b, city_j == a)) for (a,b) in flights]
        )
        s.add(flight_exists)
    
    # Check if the model is satisfiable
    if s.check() == sat:
        m = s.model()
        order_val = [m.evaluate(order[i]).as_long() for i in range(5)]
        start_val = [m.evaluate(start[i]).as_long() for i in range(5)]
        S_val = [m.evaluate(S[i]).as_long() for i in range(5)]
        
        # Generate itinerary
        itinerary = []
        for i in range(5):
            city_index = order_val[i]
            city_name = cities[city_index]
            begin_day = start_val[i]
            end_day = start_val[i] + S_val[i] - 1
            day_range = f"Day {begin_day}-{end_day}"
            itinerary.append({"day_range": day_range, "place": city_name})
        
        # Output as JSON
        import json
        print(json.dumps({"itinerary": itinerary}))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()