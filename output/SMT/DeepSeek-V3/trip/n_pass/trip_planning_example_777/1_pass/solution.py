from z3 import *
import json

def solve_itinerary():
    # Cities and their required stay days
    cities = {
        "Dublin": 5,
        "Helsinki": 3,
        "Riga": 3,
        "Reykjavik": 2,
        "Vienna": 2,
        "Tallinn": 5
    }
    city_list = list(cities.keys())
    n_days = 15
    days = range(1, n_days + 1)
    
    # Direct flights: adjacency list
    direct_flights = {
        "Helsinki": ["Riga", "Dublin", "Tallinn", "Reykjavik"],
        "Riga": ["Helsinki", "Tallinn", "Vienna", "Dublin"],
        "Vienna": ["Riga", "Reykjavik", "Dublin"],
        "Reykjavik": ["Vienna", "Helsinki", "Dublin"],
        "Tallinn": ["Dublin", "Helsinki", "Riga"],
        "Dublin": ["Riga", "Vienna", "Reykjavik", "Helsinki", "Tallinn"]
    }
    
    # Create Z3 variables: for each day, which city is visited
    # day_place[d][c] is true if on day d+1, we are in city c
    day_place = [[Bool(f"day_{d}_city_{c}") for c in city_list] for d in days]
    
    s = Solver()
    
    # Each day, at least one city is visited (could be two for flight days)
    for d in days:
        s.add(Or([day_place[d-1][i] for i in range(len(city_list))]))
    
    # Flight transitions: if on day d city A and day d+1 city B, then there must be a direct flight A->B or B->A
    for d in range(1, n_days):
        for i in range(len(city_list)):
            for j in range(len(city_list)):
                if i != j:
                    # If day d is city i and day d+1 is city j, then there must be a flight between them
                    city_i = city_list[i]
                    city_j = city_list[j]
                    s.add(Implies(
                        And(day_place[d-1][i], day_place[d][j]),
                        Or([city_j in direct_flights[city_i]])
                    ))
    
    # Stay duration constraints
    for city_idx, city in enumerate(city_list):
        total_days = sum([If(day_place[d-1][city_idx], 1, 0) for d in days])
        s.add(total_days == cities[city])
    
    # Specific constraints:
    # 1. Dublin for 5 days
    # 2. Helsinki for 3 days, with friends between day 3-5
    helsinki_idx = city_list.index("Helsinki")
    s.add(Or([day_place[d-1][helsinki_idx] for d in range(3, 6)]))
    
    # 3. Riga for 3 days
    # 4. Reykjavik for 2 days
    # 5. Vienna for 2 days, with show between day 2-3
    vienna_idx = city_list.index("Vienna")
    s.add(Or(day_place[1][vienna_idx], day_place[2][vienna_idx]))  # day 2 or 3
    
    # 6. Tallinn for 5 days, wedding between day 7-11
    tallinn_idx = city_list.index("Tallinn")
    s.add(Or([day_place[d-1][tallinn_idx] for d in range(7, 12)]))
    
    # Solve the model
    if s.check() == sat:
        model = s.model()
        itinerary = []
        
        # Determine the sequence of cities per day
        day_sequence = []
        for d in days:
            current_cities = []
            for city_idx in range(len(city_list)):
                if model.evaluate(day_place[d-1][city_idx]):
                    current_cities.append(city_list[city_idx])
            day_sequence.append(current_cities)
        
        # Generate itinerary entries
        current_stays = {}  # city: (start_day, end_day)
        
        for day in days:
            day_cities = day_sequence[day-1]
            
            # Check if this day involves a flight (multiple cities)
            if len(day_cities) > 1:
                # It's a flight day; close any ongoing stays before this day
                for city in list(current_stays.keys()):
                    start, end = current_stays[city]
                    if end == day - 1:
                        itinerary.append({"day_range": f"Day {start}-{end}", "place": city})
                        if start == end:
                            itinerary.append({"day_range": f"Day {start}", "place": city})
                        del current_stays[city]
                
                # Add flight day entries for each city
                for city in day_cities:
                    itinerary.append({"day_range": f"Day {day}", "place": city})
                
                # The next day starts new stays
                # But for cities involved in the flight, their stay may start or continue
                # For simplicity, assume the flight day is the last day for departure city and first for arrival city
                # This part may need refinement based on the model's actual assignments
            else:
                city = day_cities[0]
                if city in current_stays:
                    # Extend the current stay
                    start, _ = current_stays[city]
                    current_stays[city] = (start, day)
                else:
                    # New stay starts
                    current_stays[city] = (day, day)
        
        # Close any remaining stays after the last day
        for city, (start, end) in current_stays.items():
            itinerary.append({"day_range": f"Day {start}-{end}", "place": city})
            if start == end:
                itinerary.append({"day_range": f"Day {start}", "place": city})
        
        # Remove duplicate entries for the same day and place
        unique_itinerary = []
        seen = set()
        for entry in itinerary:
            key = (entry['day_range'], entry['place'])
            if key not in seen:
                seen.add(key)
                unique_itinerary.append(entry)
        
        return {"itinerary": unique_itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
print(json.dumps(result, indent=2))