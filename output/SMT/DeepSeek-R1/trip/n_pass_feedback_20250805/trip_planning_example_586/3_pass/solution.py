from z3 import *

def main():
    cities = ["Prague", "Lyon", "Frankfurt", "Helsinki", "Naples"]
    n_cities = len(cities)
    
    # Direct flights (undirected)
    flights = [
        (0, 1), (0, 2), (0, 3),
        (1, 2),
        (2, 3), (2, 4),
        (3, 4)
    ]
    
    # Create the solver
    s = Solver()
    
    # Variables: city[0] to city[12]
    city = [Int(f'city_{i}') for i in range(0, 13)]
    # fly[1] to fly[12]
    fly = [Bool(f'fly_{i}') for i in range(1, 13)]
    
    # Each city variable must be between 0 and 4
    for i in range(0, 13):
        s.add(city[i] >= 0, city[i] < n_cities)
    
    # Constraints for each day i from 1 to 12
    for i in range(1, 13):
        # If we don't fly, city remains the same
        no_fly_constraint = And(Not(fly[i-1]), city[i] == city[i-1])
        
        # If we fly, we must fly to a directly connected city
        fly_constraints = []
        for (a, b) in flights:
            fly_constraints.append(
                Or(
                    And(city[i-1] == a, city[i] == b),
                    And(city[i-1] == b, city[i] == a)
                )
            )
        fly_constraint = And(fly[i-1], Or(fly_constraints), city[i] != city[i-1])
        
        s.add(Or(no_fly_constraint, fly_constraint))
    
    # Exactly 4 flights
    flight_count = Sum([If(fly_i, 1, 0) for fly_i in fly])
    s.add(flight_count == 4)
    
    # Specific day constraints
    # Prague must be present on day1 and day2
    s.add(Or(city[0] == 0, city[1] == 0))  # Day1
    s.add(Or(city[1] == 0, city[2] == 0))  # Day2
    
    # Helsinki must be present on day2,3,4,5
    s.add(Or(city[1] == 3, city[2] == 3))  # Day2
    s.add(Or(city[2] == 3, city[3] == 3))  # Day3
    s.add(Or(city[3] == 3, city[4] == 3))  # Day4
    s.add(Or(city[4] == 3, city[5] == 3))  # Day5
    
    # Count the days per city
    counts = [0] * n_cities
    for c in range(n_cities):
        total = 0
        for i in range(1, 13):
            # Check if the city is present on day i (either at start or end)
            in_city = Or(city[i-1] == c, city[i] == c)
            total += If(in_city, 1, 0)
        s.add(total == [2, 3, 3, 4, 4][c])
    
    # Check for a solution
    if s.check() == sat:
        model = s.model()
        # For each day, determine the set of cities
        days_cities = []
        for day in range(1, 13):
            i = day - 1  # index for fly and city
            if model.evaluate(fly[i]):
                start_city = model.evaluate(city[i]).as_long()
                end_city = model.evaluate(city[i+1]).as_long()
                cities_on_day = {cities[start_city], cities[end_city]}
            else:
                c_val = model.evaluate(city[i+1]).as_long()
                cities_on_day = {cities[c_val]}
            days_cities.append(cities_on_day)
        
        # Map each city to the list of days it appears
        city_days = {city_name: [] for city_name in cities}
        for day_index, cities_set in enumerate(days_cities, start=1):
            for city_name in cities_set:
                city_days[city_name].append(day_index)
        
        # Group consecutive days for each city
        itinerary_ranges = []
        for city_name, days_list in city_days.items():
            if not days_list:
                continue
            days_list.sort()
            ranges = []
            start = days_list[0]
            end = days_list[0]
            for day in days_list[1:]:
                if day == end + 1:
                    end = day
                else:
                    ranges.append((start, end))
                    start = day
                    end = day
            ranges.append((start, end))
            for (start, end) in ranges:
                itinerary_ranges.append({
                    'day_range': f"Day {start}-{end}" if start != end else f"Day {start}-{start}",
                    'place': city_name
                })
        
        # Sort itinerary_ranges by the start day of each range
        itinerary_ranges.sort(key=lambda x: int(x['day_range'].split()[1].split('-')[0]))
        result = {'itinerary': itinerary_ranges}
        print(f"Plan found: {result}")
    else:
        print("No solution found")

if __name__ == '__main__':
    main()