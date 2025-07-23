from z3 import *

def solve_itinerary():
    # Cities encoding
    Krakow, Paris, Seville = 0, 1, 2
    city_names = {Krakow: 'Krakow', Paris: 'Paris', Seville: 'Seville'}
    
    # Initialize Z3 solver
    s = Solver()
    
    # Create variables for each day (1-based)
    days = 11
    city = [Int(f'city_{i}') for i in range(days)]  # 0-based for days 1-11
    
    # Each day must be one of the three cities
    for i in range(days):
        s.add(Or(city[i] == Krakow, city[i] == Paris, city[i] == Seville))
    
    # Function to count days in a city
    def count_days(city_list, c):
        return Sum([If(city_list[i] == c, 1, 0) for i in range(days)])
    
    # Function to count flight days from a city
    def count_flight_days(city_list, c):
        return Sum([If(And(i < days-1, city_list[i] == c, city_list[i+1] != c), 1, 0) for i in range(days-1)])
    
    # Total days in each city (including flight days)
    s.add(count_days(city, Seville) + count_flight_days(city, Seville) == 6)
    s.add(count_days(city, Paris) + count_flight_days(city, Paris) == 2)
    s.add(count_days(city, Krakow) + count_flight_days(city, Krakow) == 5)
    
    # Workshop constraint: at least one day in Krakow between day 1-5
    s.add(Or([city[i] == Krakow for i in range(5)]))
    
    # Flight constraints
    for i in range(days-1):
        current = city[i]
        next_c = city[i+1]
        s.add(Or(
            current == next_c,  # stay in same city
            And(current == Krakow, next_c == Paris),  # Krakow -> Paris
            And(current == Paris, next_c == Krakow),  # Paris -> Krakow
            And(current == Paris, next_c == Seville),  # Paris -> Seville
            And(current == Seville, next_c == Paris)   # Seville -> Paris
        ))
    
    # Check solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        city_list = [model.evaluate(city[i]).as_long() for i in range(days)]
        
        # Build itinerary
        current_city = city_list[0]
        start_day = 1
        for i in range(1, days):
            if city_list[i] != current_city:
                itinerary.append({'day_range': f'Day {start_day}-{i}', 'place': city_names[current_city]})
                current_city = city_list[i]
                start_day = i+1
        itinerary.append({'day_range': f'Day {start_day}-{days}', 'place': city_names[current_city]})
        
        # Verify counts
        def get_counts(city_list):
            counts = {Krakow: 0, Paris: 0, Seville: 0}
            flight_days = {Krakow: 0, Paris: 0, Seville: 0}
            for i in range(days):
                counts[city_list[i]] += 1
                if i < days-1 and city_list[i] != city_list[i+1]:
                    flight_days[city_list[i]] += 1
            return {c: counts[c] + flight_days[c] for c in counts}
        
        counts = get_counts(city_list)
        assert counts[Krakow] == 5, f"Krakow days incorrect: {counts[Krakow]}"
        assert counts[Paris] == 2, f"Paris days incorrect: {counts[Paris]}"
        assert counts[Seville] == 6, f"Seville days incorrect: {counts[Seville]}"
        
        # Verify workshop
        assert any(city_list[i] == Krakow for i in range(5)), "Workshop constraint not met"
        
        return {'itinerary': itinerary}
    else:
        return {"error": "No valid itinerary found"}

solution = solve_itinerary()
import json
print(json.dumps(solution, indent=2))