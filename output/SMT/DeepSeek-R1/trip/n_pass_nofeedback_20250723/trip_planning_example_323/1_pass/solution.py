from z3 import *

def main():
    # Define city mapping
    cities = ["London", "Oslo", "Split", "Porto"]
    city_to_int = {c: i for i, c in enumerate(cities)}
    n_days = 16
    
    # Direct flight pairs (unordered)
    direct_flights = [(0, 1), (0, 2), (1, 2), (1, 3)]
    
    # Create Z3 variables for Start and End of each day
    Start = [Int(f'Start_{i}') for i in range(n_days)]
    End = [Int(f'End_{i}') for i in range(n_days)]
    
    s = Solver()
    
    # Constraint: Start and End must be valid cities (0-3)
    for i in range(n_days):
        s.add(And(Start[i] >= 0, Start[i] < 4))
        s.add(And(End[i] >= 0, End[i] < 4))
    
    # Constraint: End of day i must be Start of day i+1 for i in 0 to 14
    for i in range(n_days - 1):
        s.add(End[i] == Start[i+1])
    
    # Constraint: If Start != End, then there must be a direct flight
    for i in range(n_days):
        start_var = Start[i]
        end_var = End[i]
        # Condition: if Start != End, then check direct flight
        flight_constraint = Or([Or(And(start_var == a, end_var == b), And(start_var == b, end_var == a)) for (a, b) in direct_flights])
        s.add(If(start_var != end_var, flight_constraint, True))
    
    # Fixed Split days: days 7 to 11 (indices 6 to 10)
    for i in [6, 7, 8, 9, 10]:
        s.add(Or(Start[i] == city_to_int["Split"], End[i] == city_to_int["Split"]))
    
    # Relatives in London: at least one day in [1,7] (indices 0 to 6) must include London
    relatives_constraint = Or([Or(Start[i] == city_to_int["London"], End[i] == city_to_int["London"]) for i in range(0, 7)])
    s.add(relatives_constraint)
    
    # Total days for each city
    total_london = 0
    total_oslo = 0
    total_split = 0
    total_porto = 0
    
    for i in range(n_days):
        # For London
        total_london += If(Start[i] == city_to_int["London"], 1, 0)
        total_london += If(And(End[i] == city_to_int["London"], Start[i] != city_to_int["London"]), 1, 0)
        
        # For Oslo
        total_oslo += If(Start[i] == city_to_int["Oslo"], 1, 0)
        total_oslo += If(And(End[i] == city_to_int["Oslo"], Start[i] != city_to_int["Oslo"]), 1, 0)
        
        # For Split
        total_split += If(Start[i] == city_to_int["Split"], 1, 0)
        total_split += If(And(End[i] == city_to_int["Split"], Start[i] != city_to_int["Split"]), 1, 0)
        
        # For Porto
        total_porto += If(Start[i] == city_to_int["Porto"], 1, 0)
        total_porto += If(And(End[i] == city_to_int["Porto"], Start[i] != city_to_int["Porto"]), 1, 0)
    
    s.add(total_london == 7)
    s.add(total_oslo == 2)
    s.add(total_split == 5)
    s.add(total_porto == 5)
    
    # Check and get model
    if s.check() == sat:
        m = s.model()
        itinerary = []
        
        for i in range(n_days):
            start_val = m.evaluate(Start[i]).as_long()
            end_val = m.evaluate(End[i]).as_long()
            day_num = i + 1
            # Add start city
            itinerary.append({"day": day_num, "city": cities[start_val]})
            # If different, add end city
            if start_val != end_val:
                itinerary.append({"day": day_num, "city": cities[end_val]})
        
        # Output as JSON
        import json
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()