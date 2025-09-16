from z3 import *

def main():
    # Create the solver
    s = Solver()
    
    # Create 13 string variables: city0 to city12
    cities = [String(f'city{i}') for i in range(13)]
    
    # Define valid city names
    city_names = ["Prague", "Helsinki", "Naples", "Frankfurt", "Lyon"]
    for i in range(13):
        s.add(Or([cities[i] == name for name in city_names]))
    
    # Allowed flight pairs (undirected, so include both directions)
    allowed_pairs = [
        ("Prague", "Lyon"),
        ("Prague", "Frankfurt"),
        ("Frankfurt", "Lyon"),
        ("Helsinki", "Naples"),
        ("Helsinki", "Frankfurt"),
        ("Naples", "Frankfurt"),
        ("Prague", "Helsinki")
    ]
    directed_allowed = []
    for (a, b) in allowed_pairs:
        directed_allowed.append((a, b))
        directed_allowed.append((b, a))
    
    # Flight constraints for each day transition
    for i in range(12):
        stay = (cities[i] == cities[i+1])
        flight_options = []
        for (a, b) in directed_allowed:
            flight_options.append(And(cities[i] == a, cities[i+1] == b))
        flight = Or(flight_options)
        s.add(Or(stay, flight))
    
    # Function to count days in a city
    def count_days(city_name):
        count = 0
        for i in range(12):  # for each day segment
            # Count if either start or end of segment is in the city
            count += If(Or(cities[i] == city_name, cities[i+1] == city_name), 1, 0)
        return count
    
    # Add constraints for total days in each city
    s.add(count_days("Prague") == 2)
    s.add(count_days("Naples") == 4)
    s.add(count_days("Helsinki") == 4)
    s.add(count_days("Frankfurt") == 3)
    s.add(count_days("Lyon") == 3)
    
    # Fixed events constraints
    s.add(cities[0] == "Prague")  # Start of day 1
    s.add(cities[1] == "Prague")  # End of day 1
    s.add(cities[2] == "Prague")  # End of day 2
    s.add(cities[3] == "Helsinki")  # End of day 3
    s.add(cities[4] == "Helsinki")  # End of day 4
    s.add(cities[5] == "Helsinki")  # End of day 5
    s.add(cities[6] == "Naples")   # End of day 6
    
    # Check and get model
    if s.check() == sat:
        m = s.model()
        itinerary = []
        current_city = None
        start_day = 1
        
        # Group consecutive days in the same city
        for day in range(1, 13):
            city_val = m.evaluate(cities[day]).as_string()
            if city_val != current_city:
                if current_city is not None:
                    # Add previous city block
                    if start_day == day - 1:
                        itinerary.append({'day_range': f'Day {start_day}', 'place': current_city})
                    else:
                        itinerary.append({'day_range': f'Day {start_day}-{day-1}', 'place': current_city})
                current_city = city_val
                start_day = day
        
        # Add the last city block
        if start_day == 12:
            itinerary.append({'day_range': f'Day 12', 'place': current_city})
        else:
            itinerary.append({'day_range': f'Day {start_day}-12', 'place': current_city})
        
        result = {'itinerary': itinerary}
        print("Plan found:", result)
    else:
        print("No valid plan found")

if __name__ == "__main__":
    main()