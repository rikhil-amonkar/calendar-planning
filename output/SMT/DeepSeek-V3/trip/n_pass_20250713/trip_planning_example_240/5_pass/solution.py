from z3 import *
import json

def solve_itinerary():
    # Cities
    Prague, Berlin, Tallinn, Stockholm = 'Prague', 'Berlin', 'Tallinn', 'Stockholm'
    cities = [Prague, Berlin, Tallinn, Stockholm]
    
    # Direct flights
    direct_flights = {
        Berlin: [Tallinn, Stockholm],
        Prague: [Tallinn, Stockholm],
        Tallinn: [Berlin, Prague, Stockholm],
        Stockholm: [Tallinn, Prague, Berlin]
    }
    
    # Create Z3 variables for each day's city
    days = 12
    day_vars = [Int(f'day_{i}') for i in range(1, days + 1)]
    
    # Mapping cities to integers
    city_to_int = {city: idx for idx, city in enumerate(cities)}
    int_to_city = {idx: city for idx, city in enumerate(cities)}
    
    solver = Solver()
    
    # Each day variable must be a valid city index
    for day_var in day_vars:
        solver.add(day_var >= 0, day_var < len(cities))
    
    # Conference in Berlin on days 6 and 8
    solver.add(day_vars[5] == city_to_int[Berlin])  # day 6 is index 5
    solver.add(day_vars[7] == city_to_int[Berlin])  # day 8 is index 7
    
    # Relatives in Tallinn between day 8 and 12 (inclusive)
    for day in range(7, 12):  # days 8-12 are indices 7 to 11
        solver.add(day_vars[day] == city_to_int[Tallinn])
    
    # Flight constraints: transitions must be between cities with direct flights
    for i in range(days - 1):
        current_day = day_vars[i]
        next_day = day_vars[i + 1]
        # Either stay in the same city or move to a directly connected city
        same_city = (current_day == next_day)
        possible_transitions = []
        for city_idx in range(len(cities)):
            current_city = int_to_city[city_idx]
            for neighbor in direct_flights[current_city]:
                neighbor_idx = city_to_int[neighbor]
                possible_transitions.append(And(current_day == city_idx, next_day == neighbor_idx))
        solver.add(Or(same_city, Or(possible_transitions)))
    
    # Count days in each city (including flight days)
    city_days = {city: 0 for city in cities}
    for city in cities:
        # Count days assigned to city
        assigned_days = Sum([If(day_var == city_to_int[city], 1, 0) for day_var in day_vars])
        # Count flights where city is departure or arrival
        flight_days = Sum([If(And(day_vars[i] == city_to_int[city], day_vars[i+1] != city_to_int[city]), 1, 0) +
                          If(And(day_vars[i] != city_to_int[city], day_vars[i+1] == city_to_int[city]), 1, 0)
                          for i in range(days - 1)])
        city_days[city] = assigned_days + flight_days
    
    # Add constraints for total days in each city
    solver.add(city_days[Prague] == 2)
    solver.add(city_days[Berlin] == 3)
    solver.add(city_days[Tallinn] == 5)
    solver.add(city_days[Stockholm] == 5)
    
    # Check if the problem is solvable
    if solver.check() == sat:
        model = solver.model()
        itinerary_days = []
        for i in range(days):
            city_idx = model.eval(day_vars[i]).as_long()
            itinerary_days.append(int_to_city[city_idx])
        
        # Generate the itinerary in the required format
        itinerary = []
        current_place = itinerary_days[0]
        start_day = 1
        
        for i in range(1, days):
            if itinerary_days[i] != itinerary_days[i - 1]:
                # Flight day: add the previous stay and the flight day entries
                end_day = i
                if start_day == end_day:
                    day_str = f"Day {start_day}"
                else:
                    day_str = f"Day {start_day}-{end_day}"
                itinerary.append({"day_range": day_str, "place": current_place})
                # Add the flight day entries (same day for departure and arrival)
                flight_day = i + 1  # since days are 1-based
                itinerary.append({"day_range": f"Day {flight_day}", "place": current_place})
                itinerary.append({"day_range": f"Day {flight_day}", "place": itinerary_days[i]})
                current_place = itinerary_days[i]
                start_day = i + 1
        
        # Add the last stay
        end_day = days
        if start_day == end_day:
            day_str = f"Day {start_day}"
        else:
            day_str = f"Day {start_day}-{end_day}"
        itinerary.append({"day_range": day_str, "place": current_place})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Execute and print the result
result = solve_itinerary()
print(json.dumps(result, indent=2))