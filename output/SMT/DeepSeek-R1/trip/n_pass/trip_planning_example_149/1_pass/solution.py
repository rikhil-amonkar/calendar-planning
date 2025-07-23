import z3
import json

def main():
    # City mapping: 0=Istanbul, 1=London, 2=Santorini
    city_map = {0: "Istanbul", 1: "London", 2: "Santorini"}
    
    # s[i] for day i+1 (0-indexed for days 0 to 9)
    s = [z3.Int(f's_{i}') for i in range(10)]
    flight = [z3.Bool(f'flight_{i}') for i in range(9)]  # flights at the end of day 1 to 9 (index 0 to 8)
    
    solver = z3.Solver()
    
    # Each s[i] must be 0, 1, or 2
    for i in range(10):
        solver.add(z3.Or(s[i] == 0, s[i] == 1, s[i] == 2))
    
    # Flight constraints for each of the 9 flights (index 0 to 8)
    for i in range(9):
        # If no flight, next day starts in the same city
        solver.add(z3.Implies(z3.Not(flight[i]), s[i] == s[i+1]))
        # If flight, the cities must be connected by a direct flight
        solver.add(z3.Implies(flight[i], 
                              z3.Or(
                                  z3.And(s[i] == 0, s[i+1] == 1),  # Istanbul <-> London
                                  z3.And(s[i] == 1, s[i+1] == 0),
                                  z3.And(s[i] == 1, s[i+1] == 2),  # London <-> Santorini
                                  z3.And(s[i] == 2, s[i+1] == 1)
                              )))
    
    # Constraints for conference days:
    # Day 5 (index 4): must be in Santorini (either start there or fly there at the end)
    solver.add(z3.Or(s[4] == 2, z3.And(flight[4], s[5] == 2)))
    # Day 10 (index 9): must start in Santorini
    solver.add(s[9] == 2)
    
    # Function to count total days for a city
    def total_days(city_code):
        total = 0
        # For days 1 to 9 (indices 0 to 8)
        for i in range(9):
            # City appears on day i+1 if: started there or flew there at the end of the day
            cond = z3.Or(s[i] == city_code, z3.And(flight[i], s[i+1] == city_code))
            total += z3.If(cond, 1, 0)
        # Day 10 (index 9): only the starting city
        total += z3.If(s[9] == city_code, 1, 0)
        return total
    
    solver.add(total_days(0) == 3)  # Istanbul
    solver.add(total_days(1) == 3)  # London
    solver.add(total_days(2) == 6)  # Santorini
    
    # Solve the constraints
    if solver.check() == z3.sat:
        m = solver.model()
        itinerary_list = []
        # Build the itinerary for each day (1 to 10)
        for day_idx in range(10):
            day_number = day_idx + 1
            # Starting city for the day
            start_city_val = m.evaluate(s[day_idx])
            start_city_int = start_city_val.as_long()
            start_city_name = city_map[start_city_int]
            itinerary_list.append({"day": day_number, "place": start_city_name})
            
            # If there's a flight at the end of this day (and it's not day 10)
            if day_idx < 9:
                flight_taken = m.evaluate(flight[day_idx])
                if z3.is_true(flight_taken):
                    next_city_val = m.evaluate(s[day_idx+1])
                    next_city_int = next_city_val.as_long()
                    next_city_name = city_map[next_city_int]
                    itinerary_list.append({"day": day_number, "place": next_city_name})
        
        result = {"itinerary": itinerary_list}
        print(json.dumps(result))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()