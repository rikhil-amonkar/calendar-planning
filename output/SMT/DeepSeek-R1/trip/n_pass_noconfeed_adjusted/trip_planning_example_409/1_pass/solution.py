from z3 import *
import json

def main():
    # Define the cities
    City, (Zurich, Hamburg, Helsinki, Bucharest, Split) = EnumSort('City', ['Zurich', 'Hamburg', 'Helsinki', 'Bucharest', 'Split'])
    city_names = {Zurich: 'Zurich', Hamburg: 'Hamburg', Helsinki: 'Helsinki', Bucharest: 'Bucharest', Split: 'Split'}
    
    # Direct flights (bidirectional)
    direct_flights = [
        (Zurich, Helsinki),
        (Hamburg, Bucharest),
        (Helsinki, Hamburg),
        (Zurich, Hamburg),
        (Zurich, Bucharest),
        (Zurich, Split),
        (Helsinki, Split),
        (Split, Hamburg)
    ]
    
    # Create arrays for start_city and end_city for 12 days (index 0 to 11代表 day1 to day12)
    start_city = [Const(f'start_city_{i}', City) for i in range(12)]
    end_city = [Const(f'end_city_{i}', City) for i in range(12)]
    
    s = Solver()
    
    # Constraint 1: For i in 1 to 11, end_city[i] equals start_city[i+1]
    for i in range(11):
        s.add(end_city[i] == start_city[i+1])
    
    # Constraint 2: If start_city[i] != end_city[i], then there must be a direct flight
    for i in range(12):
        a = start_city[i]
        b = end_city[i]
        flight_constraint = Or([Or(And(a == c1, b == c2), And(a == c2, b == c1)) for (c1, c2) in direct_flights])
        s.add(If(a != b, flight_constraint, True))
    
    # Function to count days in a city
    def count_city(c):
        total = 0
        for i in range(12):
            total += If(start_city[i] == c, 1, 0)
            total += If(And(end_city[i] == c, start_city[i] != end_city[i]), 1, 0)
        return total
    
    # City day constraints
    s.add(count_city(Hamburg) == 2)
    s.add(count_city(Zurich) == 3)
    s.add(count_city(Helsinki) == 2)
    s.add(count_city(Bucharest) == 2)
    s.add(count_city(Split) == 7)
    
    # Conference constraints: Must be in Split all day on day4 and day10
    s.add(start_city[3] == Split)  # day4
    s.add(end_city[3] == Split)    # day4
    s.add(start_city[9] == Split)  # day10
    s.add(end_city[9] == Split)    # day10
    
    # Wedding constraint: Must be in Zurich on at least one of day1, day2, or day3
    wedding_constraint = Or(
        Or(start_city[0] == Zurich, And(start_city[0] != end_city[0], end_city[0] == Zurich)),
        Or(start_city[1] == Zurich, And(start_city[1] != end_city[1], end_city[1] == Zurich)),
        Or(start_city[2] == Zurich, And(start_city[2] != end_city[2], end_city[2] == Zurich))
    )
    s.add(wedding_constraint)
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        # Extract the start_city for each day
        start_city_values = [m.evaluate(start_city[i]) for i in range(12)]
        start_city_str = [city_names[city] for city in start_city_values]
        
        # Generate itinerary segments
        itinerary = []
        current_city = start_city_str[0]
        start_day = 1
        for day_index in range(1, 12):
            if start_city_str[day_index] != current_city:
                end_day = day_index  # current segment ends at day_index (which represents day number = day_index)
                itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": current_city})
                current_city = start_city_str[day_index]
                start_day = end_day
        itinerary.append({"day_range": f"Day {start_day}-12", "place": current_city})
        
        # Output as JSON
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()