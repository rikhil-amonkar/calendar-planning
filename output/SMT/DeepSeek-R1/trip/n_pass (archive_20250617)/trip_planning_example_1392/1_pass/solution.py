from z3 import *

def main():
    # Define city names and their mapping to integers
    cities = ['Naples', 'Valencia', 'Stuttgart', 'Split', 'Venice', 'Amsterdam', 'Nice', 'Barcelona', 'Porto']
    city_map = {city: idx for idx, city in enumerate(cities)}
    
    # Define direct flight pairs
    flight_pairs = [
        ("Venice", "Nice"), ("Naples", "Amsterdam"), ("Barcelona", "Nice"), ("Amsterdam", "Nice"),
        ("Stuttgart", "Valencia"), ("Stuttgart", "Porto"), ("Split", "Stuttgart"), ("Split", "Naples"),
        ("Valencia", "Amsterdam"), ("Barcelona", "Porto"), ("Valencia", "Naples"), ("Venice", "Amsterdam"),
        ("Barcelona", "Naples"), ("Barcelona", "Valencia"), ("Split", "Amsterdam"), ("Barcelona", "Venice"),
        ("Stuttgart", "Amsterdam"), ("Naples", "Nice"), ("Venice", "Stuttgart"), ("Split", "Barcelona"),
        ("Porto", "Nice"), ("Barcelona", "Stuttgart"), ("Venice", "Naples"), ("Porto", "Amsterdam"),
        ("Porto", "Valencia"), ("Stuttgart", "Naples"), ("Barcelona", "Amsterdam")
    ]
    
    # Create set of directed flights (both directions for each pair)
    directed_edges = set()
    for a, b in flight_pairs:
        a_idx = city_map[a]
        b_idx = city_map[b]
        directed_edges.add((a_idx, b_idx))
        directed_edges.add((b_idx, a_idx))
    directed_edges = list(directed_edges)
    
    # Initialize Z3 solver
    s = Solver()
    
    # Create variables for each day: start_city and next_city
    start_city = [Int(f'start_city_{i+1}') for i in range(24)]
    next_city = [Int(f'next_city_{i+1}') for i in range(24)]
    
    # Constraint: Each city variable must be between 0 and 8
    for i in range(24):
        s.add(start_city[i] >= 0, start_city[i] < 9)
        s.add(next_city[i] >= 0, next_city[i] < 9)
    
    # Constraint: Next day's start city must be the current day's next city (for days 1 to 23)
    for i in range(23):
        s.add(start_city[i+1] == next_city[i])
    
    # Constraint: Travel must use direct flights
    for i in range(24):
        # If traveling (start_city != next_city), ensure the flight is in directed_edges
        travel_condition = start_city[i] != next_city[i]
        flight_options = []
        for (a, b) in directed_edges:
            flight_options.append(And(start_city[i] == a, next_city[i] == b))
        s.add(If(travel_condition, Or(flight_options), True)
    
    # Total travel days must be 8 (since total city-days = 24 + 8 = 32)
    travel_days = Sum([If(start_city[i] != next_city[i], 1, 0) for i in range(24)])
    s.add(travel_days == 8)
    
    # Total days per city
    totals = [0] * 9
    for c in range(9):
        total_c = 0
        for i in range(24):
            # If traveling, count both start and next cities if they match
            total_c += If(start_city[i] != next_city[i],
                          If(start_city[i] == c, 1, 0) + If(next_city[i] == c, 1, 0),
                          If(start_city[i] == c, 1, 0))
        s.add(total_c == [3, 5, 2, 5, 5, 4, 2, 2, 4][c])
    
    # Meeting in Naples between days 18-20
    naples_days = []
    for day in [17, 18, 19]:  # Indices for days 18, 19, 20
        in_naples = Or(start_city[day] == 0, And(start_city[day] != next_city[day], next_city[day] == 0))
        naples_days.append(in_naples)
    s.add(Or(naples_days))
    
    # Conference in Venice between days 6-10
    venice_days = []
    for day in [5, 6, 7, 8, 9]:  # Indices for days 6 to 10
        in_venice = Or(start_city[day] == 4, And(start_city[day] != next_city[day], next_city[day] == 4))
        venice_days.append(in_venice)
    s.add(Or(venice_days))
    
    # Meeting in Nice between days 23-24
    nice_days = []
    for day in [22, 23]:  # Indices for days 23, 24
        in_nice = Or(start_city[day] == 6, And(start_city[day] != next_city[day], next_city[day] == 6))
        nice_days.append(in_nice)
    s.add(Or(nice_days))
    
    # Workshop in Barcelona between days 5-6
    barcelona_days = []
    for day in [4, 5]:  # Indices for days 5, 6
        in_barcelona = Or(start_city[day] == 7, And(start_city[day] != next_city[day], next_city[day] == 7))
        barcelona_days.append(in_barcelona)
    s.add(Or(barcelona_days))
    
    # Check and print solution
    if s.check() == sat:
        model = s.model()
        schedule = []
        for i in range(24):
            start_val = model.evaluate(start_city[i]).as_long()
            next_val = model.evaluate(next_city[i]).as_long()
            if start_val == next_val:
                schedule.append(f"Day {i+1}: Stay in {cities[start_val]}")
            else:
                schedule.append(f"Day {i+1}: Travel from {cities[start_val]} to {cities[next_val]} (present in both)")
        print("\n".join(schedule))
        
        # Verify total days per city
        city_days = {city: 0 for city in cities}
        for i in range(24):
            start_val = model.evaluate(start_city[i]).as_long()
            next_val = model.evaluate(next_city[i]).as_long()
            city_days[cities[start_val]] += 1
            if start_val != next_val:
                city_days[cities[next_val]] += 1
        print("\nTotal days per city:")
        for city in cities:
            print(f"{city}: {city_days[city]}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()