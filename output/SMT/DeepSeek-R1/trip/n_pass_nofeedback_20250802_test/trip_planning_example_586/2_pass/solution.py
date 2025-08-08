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
    # Must be in Prague on day1 (transition 0: city0->city1) and day2 (transition 1: city1->city2)
    s.add(Or(cities[0] == "Prague", cities[1] == "Prague"))  # day1
    s.add(Or(cities[1] == "Prague", cities[2] == "Prague"))  # day2
    
    # Must be in Helsinki on days 2,3,4,5
    # Day2: transition 1 (city1->city2)
    s.add(Or(cities[1] == "Helsinki", cities[2] == "Helsinki"))
    # Day3: transition 2 (city2->city3)
    s.add(Or(cities[2] == "Helsinki", cities[3] == "Helsinki"))
    # Day4: transition 3 (city3->city4)
    s.add(Or(cities[3] == "Helsinki", cities[4] == "Helsinki"))
    # Day5: transition 4 (city4->city5)
    s.add(Or(cities[4] == "Helsinki", cities[5] == "Helsinki"))
    
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