from z3 import *

def solve_itinerary():
    # Cities
    cities = ["Zurich", "Hamburg", "Helsinki", "Bucharest", "Split"]
    city_indices = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights: adjacency list
    direct_flights = {
        "Zurich": ["Helsinki", "Hamburg", "Bucharest", "Split"],
        "Hamburg": ["Zurich", "Bucharest", "Helsinki", "Split"],
        "Helsinki": ["Zurich", "Hamburg", "Split"],
        "Bucharest": ["Zurich", "Hamburg"],
        "Split": ["Zurich", "Helsinki", "Hamburg"]
    }
    
    # Days are 1..12
    days = 12
    Day = 1
    
    # Create a Z3 solver
    s = Solver()
    
    # Variables: for each day, which city are we in?
    # day_city[d][c] is true if on day d+1 we are in city c (since days start at 1)
    day_city = [[Bool(f"day_{day}_city_{city}") for city in cities] for day in range(days)]
    
    # Constraints
    
    # 1. Each day must be in exactly one city
    for day in range(days):
        s.add(Or([day_city[day][i] for i in range(len(cities))]))
        # No two cities on the same day unless it's a flight day (handled later)
        for i in range(len(cities)):
            for j in range(i+1, len(cities)):
                s.add(Not(And(day_city[day][i], day_city[day][j])))
    
    # 2. Zurich must include days 1-3 (wedding)
    for day in [0, 1, 2]:  # days 1, 2, 3 (0-based)
        s.add(day_city[day][city_indices["Zurich"]])
    
    # 3. Split must include days 4-10 (conference)
    for day in range(3, 10):  # days 4-10 (0-based 3..9)
        s.add(day_city[day][city_indices["Split"]])
    
    # 4. Total days per city:
    # Zurich: 3 days (already includes 1-3)
    # So no additional Zurich days needed.
    # But wait, the days in Zurich could be more if flights are on those days.
    # But the problem says "visit Zurich for 3 days", which may include the wedding days.
    # So sum of days in Zurich is 3.
    zurich_days = Sum([If(day_city[day][city_indices["Zurich"]], 1, 0) for day in range(days)])
    s.add(zurich_days == 3)
    
    # Hamburg: 2 days
    hamburg_days = Sum([If(day_city[day][city_indices["Hamburg"]], 1, 0) for day in range(days)])
    s.add(hamburg_days == 2)
    
    # Helsinki: 2 days
    helsinki_days = Sum([If(day_city[day][city_indices["Helsinki"]], 1, 0) for day in range(days)])
    s.add(helsinki_days == 2)
    
    # Bucharest: 2 days
    bucharest_days = Sum([If(day_city[day][city_indices["Bucharest"]], 1, 0) for day in range(days)])
    s.add(bucharest_days == 2)
    
    # Split: 7 days (already includes days 4-10, which is 7 days)
    split_days = Sum([If(day_city[day][city_indices["Split"]], 1, 0) for day in range(days)])
    s.add(split_days == 7)
    
    # 5. Flight transitions: if day i and i+1 are in different cities, there must be a direct flight.
    for i in range(days - 1):
        for c1 in range(len(cities)):
            for c2 in range(len(cities)):
                if c1 != c2:
                    # If day i is city c1 and day i+1 is city c2, then there must be a flight between them.
                    city1 = cities[c1]
                    city2 = cities[c2]
                    if city2 not in direct_flights[city1]:
                        s.add(Not(And(day_city[i][c1], day_city[i+1][c2])))
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        # Extract the itinerary
        itinerary = []
        
        # For each day, find the city(s)
        current_cities = []
        prev_cities = []
        start_day = 1
        for day in range(days):
            day_num = day + 1
            current_cities = [city for city in cities if model.evaluate(day_city[day][city_indices[city]])]
            # Normally, current_cities should have one city, unless it's a flight day.
            # But according to the problem statement, flight days are when you're in both cities.
            # So for each day, if multiple cities are true, it's a flight day.
            if len(current_cities) > 1:
                # Flight day: add entries for each city.
                for city in current_cities:
                    itinerary.append({"day_range": f"Day {day_num}", "place": city})
            else:
                city = current_cities[0]
                # Check if this city continues from previous day
                if day == 0:
                    start_day = 1
                else:
                    prev_city_list = [c for c in cities if model.evaluate(day_city[day-1][city_indices[c]])]
                    if prev_city_list and city in prev_city_list:
                        # Same city as previous day, continue the range
                        pass
                    else:
                        # New city, add the previous range if any
                        if day > 0:
                            prev_city = [c for c in cities if model.evaluate(day_city[day-1][city_indices[c]])][0]
                            itinerary.append({"day_range": f"Day {start_day}-{day_num-1}", "place": prev_city})
                        start_day = day_num
                # Handle the last day
                if day == days - 1:
                    itinerary.append({"day_range": f"Day {start_day}-{day_num}", "place": city})
        # Now, handle any remaining ranges
        # But the above loop should have added all ranges.
        
        # Now, we need to post-process the itinerary to include flight days properly.
        # Reconstruct the itinerary more carefully.
        itinerary = []
        current_stay = None
        for day in range(days):
            day_num = day + 1
            current_cities = [city for city in cities if model.evaluate(day_city[day][city_indices[city]])]
            if len(current_cities) == 1:
                city = current_cities[0]
                if current_stay is None:
                    current_stay = (day_num, day_num, city)
                else:
                    start, end, stay_city = current_stay
                    if stay_city == city:
                        current_stay = (start, day_num, city)
                    else:
                        # Close the current stay and start a new one
                        itinerary.append({"day_range": f"Day {start}-{end}", "place": stay_city})
                        # Also, the transition day is a flight day.
                        # The previous city's last day is 'end', and the new city starts on day_num.
                        # But flight day is day_num.
                        # So add entries for both cities on day_num.
                        prev_cities = [c for c in cities if model.evaluate(day_city[day-1][city_indices[c]])]
                        if len(prev_cities) == 1:
                            prev_city = prev_cities[0]
                            itinerary.append({"day_range": f"Day {day_num}", "place": prev_city})
                        itinerary.append({"day_range": f"Day {day_num}", "place": city})
                        current_stay = (day_num, day_num, city)
            else:
                # Flight day: multiple cities.
                if current_stay is not None:
                    start, end, stay_city = current_stay
                    itinerary.append({"day_range": f"Day {start}-{end}", "place": stay_city})
                    current_stay = None
                for city in current_cities:
                    itinerary.append({"day_range": f"Day {day_num}", "place": city})
        if current_stay is not None:
            start, end, stay_city = current_stay
            itinerary.append({"day_range": f"Day {start}-{end}", "place": stay_city})
        
        # Now, ensure the itinerary is in chronological order and flight days are correctly represented.
        # The current method may have some issues with overlapping ranges, so we need to adjust.
        # Alternative approach: for each day, list all cities, and then merge consecutive days for the same city.
        daily_places = []
        for day in range(days):
            day_num = day + 1
            current_cities = [city for city in cities if model.evaluate(day_city[day][city_indices[city]])]
            daily_places.append((day_num, current_cities))
        
        itinerary = []
        i = 0
        n = len(daily_places)
        while i < n:
            day_num, cities_in_day = daily_places[i]
            if len(cities_in_day) == 1:
                city = cities_in_day[0]
                start_day = day_num
                # Look ahead to see how long this city stays.
                j = i + 1
                while j < n:
                    next_day_num, next_cities = daily_places[j]
                    if len(next_cities) == 1 and next_cities[0] == city:
                        j += 1
                    else:
                        break
                end_day = day_num + (j - i) - 1
                itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city})
                i = j
            else:
                # Flight day: multiple cities.
                for city in cities_in_day:
                    itinerary.append({"day_range": f"Day {day_num}", "place": city})
                i += 1
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
import json
print(json.dumps(result, indent=2))