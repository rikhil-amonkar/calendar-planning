from z3 import *
import json

def solve_itinerary():
    # Cities
    cities = ["Tallinn", "Bucharest", "Seville", "Stockholm", "Munich", "Milan"]
    
    # Direct flights as a dictionary for easy lookup
    direct_flights = {
        "Milan": ["Stockholm", "Munich", "Seville"],
        "Stockholm": ["Milan", "Munich", "Tallinn"],
        "Munich": ["Stockholm", "Bucharest", "Seville", "Milan", "Tallinn"],
        "Bucharest": ["Munich"],
        "Seville": ["Munich", "Milan"],
        "Tallinn": ["Stockholm", "Munich"]
    }
    
    # Days are 1..18
    days = 18
    Day = 1
    
    # Create a solver instance
    s = Solver()
    
    # Variables: for each day, which city are we in?
    # day_city[d][c] is true if we are in city c on day d
    day_city = [[Bool(f"day_{day}_city_{city}") for city in cities] for day in range(1, days+1)]
    
    # Flight variables: flight_from_to[d][i][j] is true if we fly from city i to city j on day d
    # Initialize a 3D list for flights between cities each day
    flight_from_to = [[[Bool(f"flight_{day}_{cities[i]}_{cities[j]}") 
                       for j in range(len(cities))] 
                      for i in range(len(cities))] 
                     for day in range(1, days)]
    
    # Constraints
    
    # 1. Each day, exactly one city is active (or two if it's a flight day)
    for day in range(1, days + 1):
        # On a given day, you could be in one city (no flight) or two cities (flight day)
        # So the sum of cities you're in on that day is at least 1 and at most 2.
        s.add(AtLeast(*[day_city[day-1][i] for i in range(len(cities))], 1))
        s.add(AtMost(*[day_city[day-1][i] for i in range(len(cities))], 2))
    
    # 2. Flight constraints: if you fly from city i to city j on day d, then:
    # - on day d, you are in i and j
    # - on day d-1, you were in i
    # - on day d+1, you are in j
    # Also, flights must be direct.
    for day in range(1, days):
        for i in range(len(cities)):
            for j in range(len(cities)):
                if i == j:
                    s.add(Not(flight_from_to[day-1][i][j]))  # no self-flights
                else:
                    city_i = cities[i]
                    city_j = cities[j]
                    if city_j not in direct_flights[city_i]:
                        s.add(Not(flight_from_to[day-1][i][j]))  # no indirect flights
                    else:
                        # If flight from i to j on day, then:
                        # day is in i and j, day-1 is in i, day+1 is in j
                        s.add(Implies(flight_from_to[day-1][i][j], 
                                     And(day_city[day-1][i], day_city[day][j])))
                        # Also, the previous day must be in i (unless day is 1)
                        if day > 1:
                            s.add(Implies(flight_from_to[day-1][i][j], day_city[day-2][i]))
    
    # 3. No consecutive flights: you can't have flight on day d and d+1
    for day in range(1, days - 1):
        s.add(Not(Or([And(flight_from_to[day-1][i][j], flight_from_to[day][k][l]) 
                      for i in range(len(cities)) 
                      for j in range(len(cities)) 
                      for k in range(len(cities)) 
                      for l in range(len(cities))])))
    
    # 4. Duration constraints
    # Tallinn: 2 days
    s.add(Sum([If(day_city[day][cities.index("Tallinn")], 1, 0) for day in range(days)]) == 2)
    # Bucharest: 4 days, between day 1 and 4
    b_days = Sum([If(day_city[day][cities.index("Bucharest")], 1, 0) for day in range(4)])
    s.add(b_days == 4)
    # Seville: 5 days, between day 8 and 12
    s_days = Sum([If(day_city[day][cities.index("Seville")], 1, 0) for day in range(7, 12)])
    s.add(s_days == 5)
    # Stockholm: 5 days
    s.add(Sum([If(day_city[day][cities.index("Stockholm")], 1, 0) for day in range(days)]) == 5)
    # Munich: 5 days, between day 4 and 8
    m_days = Sum([If(day_city[day][cities.index("Munich")], 1, 0) for day in range(3, 8)])
    s.add(m_days == 5)
    # Milan: 2 days
    s.add(Sum([If(day_city[day][cities.index("Milan")], 1, 0) for day in range(days)]) == 2)
    
    # 5. Initial and final constraints
    # The first day must be in Bucharest (since you visit relatives there between day 1-4)
    s.add(day_city[0][cities.index("Bucharest")])
    
    # Check if the solver can find a solution
    if s.check() == sat:
        model = s.model()
        
        # Extract the itinerary
        itinerary = []
        current_place = None
        start_day = 1
        
        # Determine the city for each day
        day_to_places = {}
        for day in range(1, days + 1):
            places = []
            for city_idx in range(len(cities)):
                if model.evaluate(day_city[day-1][city_idx]):
                    places.append(cities[city_idx])
            day_to_places[day] = places
        
        # Now, build the itinerary with day ranges
        itinerary = []
        current_places = day_to_places[1]
        start_day = 1
        current_start = 1
        
        for day in range(2, days + 1):
            next_places = day_to_places[day]
            if set(current_places) == set(next_places):
                continue
            else:
                # The current range ends at day-1
                if len(current_places) == 1:
                    place = current_places[0]
                    if current_start == day - 1:
                        itinerary.append({"day_range": f"Day {current_start}", "place": place})
                    else:
                        itinerary.append({"day_range": f"Day {current_start}-{day-1}", "place": place})
                else:
                    # Flight day: day-1 is the transition day
                    # So day-1 is part of the previous stay and the next
                    pass  # handled in the next step
                current_start = day
                current_places = next_places
        
        # Add the last segment
        if len(current_places) == 1:
            place = current_places[0]
            if current_start == days:
                itinerary.append({"day_range": f"Day {current_start}", "place": place})
            else:
                itinerary.append({"day_range": f"Day {current_start}-{days}", "place": place})
        
        # Now, reparse the day_to_places to include flight days properly
        # We need to create entries for each day, and for flight days, include both cities
        detailed_itinerary = []
        prev_places = None
        for day in range(1, days + 1):
            places = day_to_places[day]
            if len(places) == 2:
                # Flight day
                detailed_itinerary.append({"day_range": f"Day {day}", "place": places[0]})
                detailed_itinerary.append({"day_range": f"Day {day}", "place": places[1]})
            else:
                place = places[0]
                # Check if this is part of a range
                if day == 1:
                    start = day
                else:
                    prev_places_day = day_to_places[day - 1]
                    if len(prev_places_day) == 1 and prev_places_day[0] == place:
                        # Continue the same stay
                        pass
                    else:
                        start = day
                # Add the entry
                detailed_itinerary.append({"day_range": f"Day {day}", "place": place})
        
        # Now, compress consecutive days in the same city into ranges
        compressed_itinerary = []
        i = 0
        n = len(detailed_itinerary)
        while i < n:
            current = detailed_itinerary[i]
            if i < n - 1 and detailed_itinerary[i+1]['place'] == current['place'] and \
               int(detailed_itinerary[i+1]['day_range'].split(' ')[1]) == int(current['day_range'].split(' ')[1]) + 1:
                start_day = int(current['day_range'].split(' ')[1])
                j = i + 1
                while j < n and detailed_itinerary[j]['place'] == current['place'] and \
                      (j == i + 1 or int(detailed_itinerary[j]['day_range'].split(' ')[1]) == int(detailed_itinerary[j-1]['day_range'].split(' ')[1]) + 1):
                    j += 1
                end_day = int(detailed_itinerary[j-1]['day_range'].split(' ')[1])
                compressed_itinerary.append({
                    "day_range": f"Day {start_day}-{end_day}",
                    "place": current['place']
                })
                i = j
            else:
                compressed_itinerary.append(current)
                i += 1
        
        # Now, handle flight days by splitting them into individual day entries where necessary
        final_itinerary = []
        for entry in compressed_itinerary:
            day_range = entry['day_range']
            if '-' in day_range:
                start, end = map(int, day_range.split(' ')[1].split('-'))
                if start == end:
                    final_itinerary.append({"day_range": f"Day {start}", "place": entry['place']})
                else:
                    final_itinerary.append(entry)
            else:
                final_itinerary.append(entry)
        
        # Reconstruct the itinerary to include flight days properly
        # For each day, if the day is in two cities, add two entries
        final_itinerary_v2 = []
        for day in range(1, days + 1):
            places = day_to_places[day]
            for place in places:
                final_itinerary_v2.append({"day_range": f"Day {day}", "place": place})
        
        # Now, merge consecutive days in the same place into ranges
        merged_itinerary = []
        if not final_itinerary_v2:
            return {"itinerary": []}
        
        current_entry = final_itinerary_v2[0]
        start_day = int(current_entry['day_range'].split(' ')[1])
        current_place = current_entry['place']
        
        for entry in final_itinerary_v2[1:]:
            day = int(entry['day_range'].split(' ')[1])
            place = entry['place']
            if place == current_place and day == start_day + 1:
                start_day += 1
            else:
                if start_day == int(current_entry['day_range'].split(' ')[1]):
                    merged_itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
                else:
                    merged_itinerary.append({"day_range": f"Day {int(current_entry['day_range'].split(' ')[1])}-{start_day}", "place": current_place})
                current_entry = entry
                start_day = day
                current_place = place
        
        # Add the last entry
        if start_day == int(current_entry['day_range'].split(' ')[1]):
            merged_itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
        else:
            merged_itinerary.append({"day_range": f"Day {int(current_entry['day_range'].split(' ')[1])}-{start_day}", "place": current_place})
        
        # Now, for flight days (days with two entries), ensure both are present
        # So, for each day in day_to_places, if len(places) == 2, then both are in merged_itinerary as separate entries for that day.
        # So, no merging across different places.
        
        # The merged_itinerary should already have this because each day's entries are added separately in final_itinerary_v2.
        
        return {"itinerary": merged_itinerary}
    else:
        return {"itinerary": []}

# Execute the function and print the result
result = solve_itinerary()
print(json.dumps(result, indent=2))