from z3 import *

def main():
    # Create the solver
    s = Solver()
    
    # Create 13 string variables: city0 to city12
    cities = [String(f'city{i}') for i in range(13)]
    
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
    
    # Flight constraints for each day transition (from city_i to city_{i+1})
    for i in range(12):
        # Either stay in the same city or take a direct flight
        stay = (cities[i] == cities[i+1])
        flight_options = []
        for (a, b) in directed_allowed:
            flight_options.append(And(cities[i] == a, cities[i+1] == b))
        flight = Or(flight_options)
        s.add(Or(stay, flight))
    
    # Function to count days in a city
    def count_days(city_name):
        count = 0
        for i in range(12):  # for each day transition (day i+1)
            # The day is spent in the city if the start or end of the day is in the city
            count += If(Or(cities[i] == city_name, cities[i+1] == city_name), 1, 0)
        return count
    
    # Add constraints for the number of days in each city
    s.add(count_days("Prague") == 2)
    s.add(count_days("Naples") == 4)
    s.add(count_days("Helsinki") == 4)
    s.add(count_days("Frankfurt") == 3)
    s.add(count_days("Lyon") == 3)
    
    # Fixed events: 
    # Must be in Prague at the start (city0) and through day1
    s.add(cities[0] == "Prague")
    s.add(cities[1] == "Prague")
    
    # Day2: must end in Helsinki (since we start in Prague and need to be in Helsinki for day2)
    s.add(cities[2] == "Helsinki")
    
    # Must be in Helsinki on days 3,4,5 (days 3 and 4 stay in Helsinki, day5 can stay or move)
    s.add(cities[3] == "Helsinki")
    s.add(cities[4] == "Helsinki")
    s.add(Or(cities[5] == "Helsinki", cities[5] == "Naples"))  # Day5: can stay in Helsinki or go to Naples
    
    # Check and get model
    if s.check() == sat:
        m = s.model()
        itinerary_list = []
        # For each day from 1 to 12, the location is the end city of that day (city_i for day i)
        for day in range(1, 13):
            # Get the value of the city at the end of the day (cities[day])
            city_val = m.evaluate(cities[day])
            itinerary_list.append({"day": day, "location": city_val.as_string()})
        
        result = {"itinerary": itinerary_list}
        print(result)
    else:
        print("Unsatisfiable")

if __name__ == "__main__":
    main()