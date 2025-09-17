import json
from z3 import *

def main():
    # Define cities and mapping to integers
    cities = ["Brussels", "Helsinki", "Split", "Dubrovnik", "Istanbul", "Milan", "Vilnius", "Frankfurt"]
    city_to_int = {city: idx for idx, city in enumerate(cities)}
    
    # Define direct flights as set of tuples (city1_index, city2_index)
    direct_flights_set = {
        (city_to_int["Milan"], city_to_int["Frankfurt"]),
        (city_to_int["Split"], city_to_int["Frankfurt"]),
        (city_to_int["Milan"], city_to_int["Split"]),
        (city_to_int["Brussels"], city_to_int["Vilnius"]),
        (city_to_int["Brussels"], city_to_int["Helsinki"]),
        (city_to_int["Istanbul"], city_to_int["Brussels"]),
        (city_to_int["Milan"], city_to_int["Vilnius"]),
        (city_to_int["Brussels"], city_to_int["Milan"]),
        (city_to_int["Istanbul"], city_to_int["Helsinki"]),
        (city_to_int["Helsinki"], city_to_int["Vilnius"]),
        (city_to_int["Helsinki"], city_to_int["Dubrovnik"]),
        (city_to_int["Split"], city_to_int["Vilnius"]),
        (city_to_int["Dubrovnik"], city_to_int["Istanbul"]),
        (city_to_int["Istanbul"], city_to_int["Milan"]),
        (city_to_int["Helsinki"], city_to_int["Frankfurt"]),
        (city_to_int["Istanbul"], city_to_int["Vilnius"]),
        (city_to_int["Split"], city_to_int["Helsinki"]),
        (city_to_int["Milan"], city_to_int["Helsinki"]),
        (city_to_int["Istanbul"], city_to_int["Frankfurt"]),
        (city_to_int["Brussels"], city_to_int["Frankfurt"]),
        (city_to_int["Dubrovnik"], city_to_int["Frankfurt"]),
        (city_to_int["Frankfurt"], city_to_int["Vilnius"])
    }
    # Ensure symmetric flights
    direct_flights = set()
    for (a, b) in direct_flights_set:
        direct_flights.add((a, b))
        direct_flights.add((b, a))
    
    # Initialize solver
    solver = Solver()
    
    # Variables for each day (1 to 22): city at start of day
    city_day = [Int(f'city_day_{i}') for i in range(1, 23)]
    # Variables for each day (1 to 21): whether we flew that day
    flew = [Bool(f'flew_{i}') for i in range(1, 22)]
    
    # Constraint: city_day must be between 0 and 7
    for i in range(22):
        solver.add(city_day[i] >= 0, city_day[i] < 8)
    
    # Constraints for flew and city transitions
    for i in range(21):
        # If not flew, then city remains same
        solver.add(If(flew[i], True, city_day[i] == city_day[i+1]))
        # If flew, cities must be different and have direct flight
        solver.add(If(flew[i], 
                      And(city_day[i] != city_day[i+1], 
                          Or([And(city_day[i] == a, city_day[i+1] == b) for (a, b) in direct_flights])),
                      True))
    
    # Presence function: for day i and city c, presence is true if:
    # - city_day[i] == c, or
    # - (i < 21 and flew[i] and city_day[i+1] == c)
    def presence(day_idx, city_idx):
        day = day_idx - 1  # convert to 0-indexed
        conditions = [city_day[day] == city_idx]
        if day < 21:
            conditions.append(And(flew[day], city_day[day+1] == city_idx))
        return Or(conditions)
    
    # Fixed events constraints
    istanbul_idx = city_to_int["Istanbul"]
    vilnius_idx = city_to_int["Vilnius"]
    frankfurt_idx = city_to_int["Frankfurt"]
    
    # Istanbul days 1-5
    for day in range(1, 6):
        solver.add(presence(day, istanbul_idx))
    # Vilnius days 18-22
    for day in range(18, 23):
        solver.add(presence(day, vilnius_idx))
    # Frankfurt days 16-18
    for day in range(16, 19):
        solver.add(presence(day, frankfurt_idx))
    
    # Total days per city constraints
    required_days = {
        "Brussels": 3,
        "Helsinki": 3,
        "Split": 4,
        "Dubrovnik": 2,
        "Istanbul": 5,
        "Milan": 4,
        "Vilnius": 5,
        "Frankfurt": 3
    }
    
    for city, total_days in required_days.items():
        c_idx = city_to_int[city]
        solver.add(Sum([If(presence(day, c_idx), 1, 0) for day in range(1, 23)]) == total_days)
    
    # Total flight days must be 7
    solver.add(Sum([If(flew[i], 1, 0) for i in range(21)]) == 7)
    
    # Check satisfaction
    if solver.check() == sat:
        model = solver.model()
        
        # Extract presence for each day and city
        presence_matrix = {}
        for day in range(1, 23):
            presence_matrix[day] = []
            for city_idx in range(8):
                if is_true(model.eval(presence(day, city_idx))):
                    presence_matrix[day].append(cities[city_idx])
        
        # Build itinerary by grouping consecutive days per city
        itinerary_entries = []
        for city in cities:
            days_in_city = [day for day in range(1, 23) if city in presence_matrix[day]]
            if not days_in_city:
                continue
            # Group consecutive days
            groups = []
            start = days_in_city[0]
            prev = days_in_city[0]
            for current in days_in_city[1:]:
                if current == prev + 1:
                    prev = current
                else:
                    groups.append((start, prev))
                    start = current
                    prev = current
            groups.append((start, prev))
            
            for (start, end) in groups:
                day_range = f"Day {start}-{end}" if start != end else f"Day {start}"
                itinerary_entries.append({"day_range": day_range, "place": city})
        
        # Sort entries by start day
        itinerary_entries.sort(key=lambda x: int(x['day_range'].split(' ')[1].split('-')[0]))
        
        # Output as JSON
        result = {"itinerary": itinerary_entries}
        print(json.dumps(result, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()