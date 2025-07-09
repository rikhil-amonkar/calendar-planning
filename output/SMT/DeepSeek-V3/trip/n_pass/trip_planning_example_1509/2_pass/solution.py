from z3 import *
import json

def solve_itinerary():
    # Cities to visit
    cities = ["Paris", "Warsaw", "Krakow", "Tallinn", "Riga", "Copenhagen", 
              "Helsinki", "Oslo", "Santorini", "Lyon"]
    
    # Direct flights as per the problem statement (assuming all are bidirectional)
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
        direct_flights[a].add(b)
        direct_flights[b].add(a)
    
    # Now, proceed with Z3
    s = Solver()
    
    # Create day variables: day_1 to day_25, each can be one of the cities
    days = [Int(f"day_{i}") for i in range(1, 26)]
    for day in days:
        s.add(Or([day == cities.index(c) for c in cities]))
    
    # Helper functions
    def city_index(city):
        return cities.index(city)
    
    def city_visited_for_days(city, total_days):
        """Assert that the city appears exactly total_days times in the itinerary."""
        s.add(Sum([If(days[i] == city_index(city), 1, 0) for i in range(25)]) == total_days)
    
    # Apply constraints
    
    # Paris: 5 days total, with friends between day 4 and 8 (so at least one day between 4-8 is Paris)
    city_visited_for_days("Paris", 5)
    s.add(Or([days[i] == city_index("Paris") for i in range(3, 8)]))  # days 4-8 (0-based 3-7)
    
    # Warsaw: 2 days
    city_visited_for_days("Warsaw", 2)
    
    # Krakow: 2 days, workshop between day 17-18 (so days 16 or 17 must be Krakow)
    city_visited_for_days("Krakow", 2)
    s.add(Or(days[16] == city_index("Krakow"), days[17] == city_index("Krakow")))
    
    # Tallinn: 2 days
    city_visited_for_days("Tallinn", 2)
    
    # Riga: 2 days, wedding between day 23-24 (days 22 or 23 must be Riga)
    city_visited_for_days("Riga", 2)
    s.add(Or(days[22] == city_index("Riga"), days[23] == city_index("Riga")))
    
    # Copenhagen: 5 days
    city_visited_for_days("Copenhagen", 5)
    
    # Helsinki: 5 days, meet friend between day 18-22 (days 17-21 must include Helsinki)
    city_visited_for_days("Helsinki", 5)
    s.add(Or([days[i] == city_index("Helsinki") for i in range(17, 22)]))
    
    # Oslo: 5 days
    city_visited_for_days("Oslo", 5)
    
    # Santorini: 2 days, relatives between day 12-13 (days 11 or 12 must be Santorini)
    city_visited_for_days("Santorini", 2)
    s.add(Or(days[11] == city_index("Santorini"), days[12] == city_index("Santorini")))
    
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
        
        # Add the last stay
        if start_day == 25:
            itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
        else:
            itinerary.append({"day_range": f"Day {start_day}-25", "place": current_place})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Execute the function and print the result
result = solve_itinerary()
print(json.dumps(result, indent=2))