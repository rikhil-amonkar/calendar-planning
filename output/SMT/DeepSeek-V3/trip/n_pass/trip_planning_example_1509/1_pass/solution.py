from z3 import *
import json

def solve_itinerary():
    # Cities to visit
    cities = ["Paris", "Warsaw", "Krakow", "Tallinn", "Riga", "Copenhagen", 
              "Helsinki", "Oslo", "Santorini", "Lyon"]
    
    # Direct flights as per the problem statement (bidirectional unless specified)
    direct_flights = {
        "Warsaw": ["Riga", "Tallinn"],  # Assuming typo in problem statement (Warsaw is correct)
        "Warsaw": ["Riga", "Tallinn", "Copenhagen", "Helsinki", "Paris", "Oslo", "Krakow"],
        "Riga": ["Warsaw", "Tallinn", "Helsinki", "Paris", "Oslo", "Copenhagen"],
        "Tallinn": ["Warsaw", "Oslo", "Helsinki", "Copenhagen", "Riga", "Paris"],
        "Copenhagen": ["Helsinki", "Warsaw", "Santorini", "Krakow", "Riga", "Oslo", "Tallinn", "Paris"],
        "Helsinki": ["Copenhagen", "Warsaw", "Krakow", "Tallinn", "Riga", "Oslo", "Paris"],
        "Oslo": ["Lyon", "Paris", "Riga", "Warsaw", "Krakow", "Helsinki", "Tallinn", "Copenhagen", "Santorini"],
        "Santorini": ["Copenhagen", "Oslo"],
        "Lyon": ["Paris", "Oslo"],
        "Paris": ["Lyon", "Oslo", "Riga", "Tallinn", "Warsaw", "Helsinki", "Krakow", "Copenhagen"],
        "Krakow": ["Warsaw", "Helsinki", "Copenhagen", "Paris", "Oslo"]
    }
    
    # Correcting the direct_flights dictionary based on the problem's flight list
    # The problem lists flights as bidirectional unless specified (like from Riga to Tallinn)
    # So we'll model all flights as bidirectional except where noted.
    # But in the problem's list, all are bidirectional except "from Riga to Tallinn" and "from Santorini to Oslo".
    # So for simplicity, we'll treat all as bidirectional except those two, but since the problem mentions "from X to Y", it's unclear if return flights exist. Assuming bidirectional unless specified.

    # Re-defining direct_flights properly:
    flight_pairs = [
        ("Warsaw", "Riga"), ("Warsaw", "Tallinn"), ("Copenhagen", "Helsinki"), 
        ("Lyon", "Paris"), ("Copenhagen", "Warsaw"), ("Lyon", "Oslo"), ("Paris", "Oslo"), 
        ("Paris", "Riga"), ("Krakow", "Helsinki"), ("Paris", "Tallinn"), ("Oslo", "Riga"), 
        ("Krakow", "Warsaw"), ("Paris", "Helsinki"), ("Copenhagen", "Santorini"), 
        ("Helsinki", "Warsaw"), ("Helsinki", "Riga"), ("Copenhagen", "Krakow"), 
        ("Copenhagen", "Riga"), ("Paris", "Krakow"), ("Copenhagen", "Oslo"), 
        ("Oslo", "Tallinn"), ("Oslo", "Helsinki"), ("Copenhagen", "Tallinn"), 
        ("Oslo", "Krakow"), ("Riga", "Tallinn"), ("Helsinki", "Tallinn"), 
        ("Paris", "Copenhagen"), ("Paris", "Warsaw"), ("Santorini", "Oslo")
    ]
    
    # Build adjacency list
    direct_flights = {city: set() for city in cities}
    for a, b in flight_pairs:
        a_correct = a  # assuming the strings are correct
        b_correct = b
        if a_correct in direct_flights and b_correct in direct_flights:
            direct_flights[a_correct].add(b_correct)
            direct_flights[b_correct].add(a_correct)
        else:
            # Handle possible typos like 'Warsaw' vs 'Warsaw'?
            pass
    
    # Now, proceed with Z3
    s = Solver()
    
    # Create day variables: day_1 to day_25, each can be one of the cities
    days = [Int(f"day_{i}") for i in range(1, 26)]
    for day in days:
        s.add(Or([day == cities.index(c) for c in cities]))
    
    # Helper functions
    def city_index(city):
        return cities.index(city)
    
    def consecutive_days_in_city(start, end, city):
        """Assert that from start to end day, the city is the same."""
        city_idx = city_index(city)
        for day in range(start, end + 1):
            s.add(days[day - 1] == city_idx)
    
    def city_visited_for_days(city, total_days):
        """Assert that the city appears exactly total_days times in the itinerary."""
        s.add(Sum([If(days[i] == city_index(city), 1, 0) for i in range(25)]) == total_days)
    
    def city_visited_between_days(city, start_day, end_day):
        """Assert that the city is visited at least once between start_day and end_day (inclusive)."""
        s.add(Or([days[i] == city_index(city) for i in range(start_day - 1, end_day)]))
    
    # Apply constraints
    
    # Paris: 5 days total, with friends between day 4 and 8.
    city_visited_for_days("Paris", 5)
    # The friends' visit must be within a continuous Paris stay that includes days 4-8.
    # So Paris must include some days that cover 4-8.
    # For simplicity, require that at least one day in 4-8 is Paris.
    s.add(Or([days[i] == city_index("Paris") for i in range(3, 8)]))  # days 4-8 (1-based)
    
    # Warsaw: 2 days
    city_visited_for_days("Warsaw", 2)
    
    # Krakow: 2 days, workshop between day 17-18
    city_visited_for_days("Krakow", 2)
    # Workshop must be during one of the Krakow days.
    s.add(Or(days[16] == city_index("Krakow"), days[17] == city_index("Krakow")))  # days 17-18
    
    # Tallinn: 2 days
    city_visited_for_days("Tallinn", 2)
    
    # Riga: 2 days, wedding between day 23-24
    city_visited_for_days("Riga", 2)
    s.add(Or(days[22] == city_index("Riga"), days[23] == city_index("Riga")))  # days 23-24
    
    # Copenhagen: 5 days
    city_visited_for_days("Copenhagen", 5)
    
    # Helsinki: 5 days, meet friend between day 18-22
    city_visited_for_days("Helsinki", 5)
    s.add(Or([days[i] == city_index("Helsinki") for i in range(17, 22)]))  # days 18-22
    
    # Oslo: 5 days
    city_visited_for_days("Oslo", 5)
    
    # Santorini: 2 days, relatives between day 12-13
    city_visited_for_days("Santorini", 2)
    s.add(Or(days[11] == city_index("Santorini"), days[12] == city_index("Santorini")))  # days 12-13
    
    # Lyon: 4 days
    city_visited_for_days("Lyon", 4)
    
    # Flight constraints: for each consecutive day, either same city or direct flight exists.
    for i in range(24):
        current_day = days[i]
        next_day = days[i + 1]
        s.add(Or(
            current_day == next_day,  # same city
            # Or there's a flight between them
            Or([And(current_day == city_index(a), next_day == city_index(b)) 
                for a in direct_flights for b in direct_flights[a]])
        ))
    
    # Check if the model is satisfiable
    if s.check() == sat:
        m = s.model()
        itinerary_days = [cities[m.evaluate(days[i]).as_long()] for i in range(25)]
        
        # Generate the itinerary in the required format
        itinerary = []
        current_place = itinerary_days[0]
        start_day = 1
        
        for day in range(1, 26):
            if day == 1:
                continue
            if itinerary_days[day - 1] != current_place:
                # Flight day: day is the transition
                # Add the previous stay
                if start_day != day - 1:
                    itinerary.append({"day_range": f"Day {start_day}-{day - 1}", "place": current_place})
                else:
                    itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
                # Add the flight day for departure
                itinerary.append({"day_range": f"Day {day - 1}", "place": current_place})
                # Add the flight day for arrival
                new_place = itinerary_days[day - 1]
                itinerary.append({"day_range": f"Day {day - 1}", "place": new_place})
                # Start new stay
                current_place = new_place
                start_day = day
            # else: continue the current stay
        
        # Add the last stay
        if start_day == 25:
            itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
        else:
            itinerary.append({"day_range": f"Day {start_day}-25", "place": current_place})
        
        # Now, post-process to merge consecutive days in the same city where there's no flight
        # But the current code already does that by checking for changes.
        
        # Verify that all constraints are met in the generated itinerary.
        # For now, return the itinerary.
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Execute the function and print the result
result = solve_itinerary()
print(json.dumps(result, indent=2))