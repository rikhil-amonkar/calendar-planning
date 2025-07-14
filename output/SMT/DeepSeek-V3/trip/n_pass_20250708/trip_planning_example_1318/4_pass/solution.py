from z3 import *

def solve_itinerary():
    # Cities
    cities = ["Oslo", "Helsinki", "Edinburgh", "Riga", "Tallinn", "Budapest", "Vilnius", "Porto", "Geneva"]
    
    # Direct flights as a dictionary: key is source, value is list of destinations
    direct_flights = {
        "Porto": ["Oslo", "Edinburgh", "Geneva"],
        "Edinburgh": ["Budapest", "Geneva", "Porto", "Oslo", "Helsinki", "Riga"],
        "Riga": ["Tallinn", "Oslo", "Helsinki", "Vilnius"],
        "Tallinn": ["Vilnius", "Helsinki", "Oslo"],
        "Vilnius": ["Helsinki", "Oslo"],
        "Helsinki": ["Vilnius", "Budapest", "Oslo", "Geneva"],
        "Budapest": ["Geneva", "Oslo"],
        "Geneva": ["Oslo", "Porto", "Budapest"],
        "Oslo": ["Porto", "Riga", "Geneva", "Edinburgh", "Vilnius", "Tallinn", "Helsinki", "Budapest"]
    }
    
    # Total days
    total_days = 25
    
    # Create a Z3 solver instance
    solver = Solver()
    
    # Create variables: day_i represents the city on day i (1-based)
    day_vars = [Int(f"day_{i}") for i in range(1, total_days + 1)]
    
    # Map each city to an integer
    city_to_int = {city: idx for idx, city in enumerate(cities)}
    int_to_city = {idx: city for idx, city in enumerate(cities)}
    
    # Add constraints: each day_var must be between 0 and 8 (inclusive)
    for day in day_vars:
        solver.add(day >= 0, day < len(cities))
    
    # Constraints for transitions: consecutive days must be the same city or have a direct flight
    for i in range(total_days - 1):
        current_city = day_vars[i]
        next_city = day_vars[i + 1]
        # Create OR condition for all possible direct flights
        flight_options = []
        for src in direct_flights:
            for dst in direct_flights[src]:
                flight_options.append(And(current_city == city_to_int[src], next_city == city_to_int[dst]))
        solver.add(Or(current_city == next_city, *flight_options))
    
    # Constraints for total days in each city
    required_days = {
        "Oslo": 2,
        "Helsinki": 2,
        "Edinburgh": 3,
        "Riga": 2,
        "Tallinn": 5,
        "Budapest": 5,
        "Vilnius": 5,
        "Porto": 5,
        "Geneva": 4
    }
    
    for city in cities:
        count = Sum([If(day == city_to_int[city], 1, 0) for day in day_vars])
        solver.add(count == required_days[city])
    
    # Special constraints:
    # Wedding in Tallinn between day 4 and day 8: at least one day in Tallinn in this range
    tallinn_days = [If(day_vars[i] == city_to_int["Tallinn"], 1, 0) for i in range(3, 8)]  # days 4-8 (0-based 3-7)
    solver.add(Sum(tallinn_days) >= 1)
    
    # Meet friend in Oslo between day 24 and 25
    solver.add(Or(day_vars[23] == city_to_int["Oslo"], day_vars[24] == city_to_int["Oslo"]))  # days 24 and 25
    
    # Check if the solver can find a solution
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        
        # Determine the sequence of cities from the model
        sequence = []
        for i in range(total_days):
            city_idx = model.evaluate(day_vars[i]).as_long()
            sequence.append(int_to_city[city_idx])
        
        # Generate the itinerary in the required format
        current_place = sequence[0]
        start_day = 1
        for i in range(1, total_days):
            if sequence[i] != sequence[i-1]:
                # Flight day: i+1 is the day of flight (1-based)
                # Add the stay before the flight
                if start_day != i:
                    itinerary.append({"day_range": f"Day {start_day}-{i}", "place": current_place})
                else:
                    itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
                # Add the flight day for departure and arrival
                itinerary.append({"day_range": f"Day {i+1}", "place": current_place})
                itinerary.append({"day_range": f"Day {i+1}", "place": sequence[i]})
                current_place = sequence[i]
                start_day = i + 1
        # Add the last stay
        if start_day <= total_days:
            if start_day == total_days:
                itinerary.append({"day_range": f"Day {total_days}", "place": current_place})
            else:
                itinerary.append({"day_range": f"Day {start_day}-{total_days}", "place": current_place})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Generate the itinerary
itinerary = solve_itinerary()
print(itinerary)