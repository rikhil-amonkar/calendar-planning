from z3 import *
import json

def main():
    # Define cities and required days
    cities = ["Salzburg", "Venice", "Bucharest", "Brussels", "Hamburg", "Copenhagen", "Nice", "Zurich", "Naples"]
    required_days = {
        "Salzburg": 2,
        "Venice": 5,
        "Bucharest": 4,
        "Brussels": 2,
        "Hamburg": 4,
        "Copenhagen": 4,
        "Nice": 3,
        "Zurich": 5,
        "Naples": 4
    }
    
    # Define direct flights
    direct_flights_str = "Zurich and Brussels, Bucharest and Copenhagen, Venice and Brussels, Nice and Zurich, Hamburg and Nice, Zurich and Naples, Hamburg and Bucharest, Zurich and Copenhagen, Bucharest and Brussels, Hamburg and Brussels, Venice and Naples, Venice and Copenhagen, Bucharest and Naples, Hamburg and Copenhagen, Venice and Zurich, Nice and Brussels, Hamburg and Venice, Copenhagen and Naples, Nice and Naples, Hamburg and Zurich, Salzburg and Hamburg, Zurich and Bucharest, Brussels and Naples, Copenhagen and Brussels, Venice and Nice, Nice and Copenhagen"
    flights = direct_flights_str.split(", ")
    direct_flights = []
    for f in flights:
        parts = f.split(" and ")
        if len(parts) == 2:
            direct_flights.append((parts[0], parts[1]))
    
    # Create set of connected city pairs (both directions)
    connected = set()
    for (c1, c2) in direct_flights:
        connected.add((c1, c2))
        connected.add((c2, c1))
    
    # Initialize Z3 solver and variables
    solver = Solver()
    in_city = {}  # Dictionary: key (day, city) -> Z3 Bool
    for day in range(1, 26):
        for city in cities:
            in_city[(day, city)] = Bool(f"day{day}_{city}")
    
    # Constraints for each day
    for day in range(1, 26):
        day_vars = [in_city[(day, c)] for c in cities]
        # At least one city per day
        solver.add(Or(day_vars))
        # At most two cities per day
        solver.add(Sum([If(var, 1, 0) for var in day_vars]) <= 2)
        # If two cities, they must be connected
        for i in range(len(cities)):
            for j in range(i+1, len(cities)):
                c1 = cities[i]
                c2 = cities[j]
                if (c1, c2) not in connected:
                    solver.add(Not(And(in_city[(day, c1)], in_city[(day, c2)])))
    
    # Consecutive days must share at least one city
    for day in range(1, 25):
        solver.add(Or([And(in_city[(day, c)], in_city[(day+1, c)]) for c in cities]))
    
    # Total days per city
    for city in cities:
        total = Sum([If(in_city[(d, city)], 1, 0) for d in range(1, 26)])
        solver.add(total == required_days[city])
    
    # Specific constraints
    # Brussels on days 21 and 22
    solver.add(in_city[(21, "Brussels")])
    solver.add(in_city[(22, "Brussels")])
    # Copenhagen between days 18-21 (inclusive)
    solver.add(Or([in_city[(d, "Copenhagen")] for d in range(18, 22)]))
    # Nice between days 9-11 (inclusive)
    solver.add(Or([in_city[(d, "Nice")] for d in range(9, 12)]))
    # Naples between days 22-25 (inclusive)
    solver.add(Or([in_city[(d, "Naples")] for d in range(22, 26)]))
    
    # Check and get model
    if solver.check() == sat:
        model = solver.model()
        # Extract city presence for each day
        presence = {}
        for day in range(1, 26):
            for city in cities:
                if is_true(model.eval(in_city[(day, city)])):
                    if day not in presence:
                        presence[day] = []
                    presence[day].append(city)
        
        # Create intervals for each city
        city_intervals = {city: [] for city in cities}
        for city in cities:
            start = None
            for day in range(1, 26):
                if day in presence and city in presence[day]:
                    if start is None:
                        start = day
                else:
                    if start is not None:
                        city_intervals[city].append((start, day-1))
                        start = None
            if start is not None:
                city_intervals[city].append((start, 25))
        
        # Generate itinerary list
        itinerary = []
        for city in cities:
            for (start, end) in city_intervals[city]:
                if start == end:
                    day_range = f"Day {start}"
                else:
                    day_range = f"Day {start}-{end}"
                itinerary.append({"day_range": day_range, "place": city})
        
        # Sort itinerary by start day
        itinerary.sort(key=lambda x: int(x['day_range'].split(' ')[1].split('-')[0]))
        
        # Output as JSON
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()