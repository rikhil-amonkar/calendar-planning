from z3 import *
import json

def solve_itinerary():
    # Cities and their required days
    cities = {
        "Dublin": 3,
        "Madrid": 2,
        "Oslo": 3,
        "London": 2,
        "Vilnius": 3,
        "Berlin": 5
    }
    
    # Direct flights
    direct_flights = [
        ("London", "Madrid"),
        ("Oslo", "Vilnius"),
        ("Berlin", "Vilnius"),
        ("Madrid", "Oslo"),
        ("Madrid", "Dublin"),
        ("London", "Oslo"),
        ("Madrid", "Berlin"),
        ("Berlin", "Oslo"),
        ("Dublin", "Oslo"),
        ("London", "Dublin"),
        ("London", "Berlin"),
        ("Berlin", "Dublin")
    ]
    
    # Create bidirectional flights
    flights = set()
    for a, b in direct_flights:
        flights.add((a, b))
        flights.add((b, a))
    
    # Days are 1..13
    days = 13
    
    # Create a solver
    s = Solver()
    
    # Variables: for each day, which city are we in?
    # city_day[d][c] is true if we are in city c on day d
    city_day = [[Bool(f"city_{c}_day_{d}") for c in cities] for d in range(1, days + 1)]
    city_index = {c: i for i, c in enumerate(cities)}
    
    # Each day, at least one city is active, and no more than two.
    for d in range(days):
        day = d + 1
        s.add(Or([city_day[d][i] for i in range(len(cities))]))
        # No three cities active on the same day.
        for i in range(len(cities)):
            for j in range(i+1, len(cities)):
                for k in range(j+1, len(cities)):
                    s.add(Not(And(city_day[d][i], city_day[d][j], city_day[d][k])))
    
    # Flight constraints: if two cities are active on the same day, they must have a direct flight
    for d in range(days):
        day = d + 1
        for i in range(len(cities)):
            for j in range(i+1, len(cities)):
                c1 = list(cities.keys())[i]
                c2 = list(cities.keys())[j]
                s.add(Implies(And(city_day[d][i], city_day[d][j]), (c1, c2) in flights or (c2, c1) in flights))
    
    # Total days per city
    for c in cities:
        total = 0
        for d in range(days):
            day = d + 1
            total += If(city_day[d][city_index[c]], 1, 0)
        s.add(total == cities[c])
    
    # Dublin: 3 days, days 7-9.
    for d in [6, 7, 8]:  # days 7, 8, 9
        s.add(city_day[d][city_index["Dublin"]] == True)
    
    # Madrid: 2 days, days 2 and 3.
    s.add(city_day[1][city_index["Madrid"]] == True)  # day 2
    s.add(city_day[2][city_index["Madrid"]] == True)  # day 3
    
    # Berlin: 5 days, days 3-7.
    for d in [2, 3, 4, 5, 6]:  # days 3, 4, 5, 6, 7
        s.add(city_day[d][city_index["Berlin"]] == True)
    
    # Check if the model is satisfiable
    if s.check() == sat:
        m = s.model()
        itinerary = []
        
        # Determine for each day which cities are active
        day_places = {}
        for d in range(days):
            day = d + 1
            active = []
            for c in cities:
                if is_true(m.evaluate(city_day[d][city_index[c]])):
                    active.append(c)
            day_places[day] = active
        
        # Now, build the itinerary
        current_place = None
        start_day = 1
        for day in range(1, days + 1):
            places = day_places[day]
            if len(places) == 1:
                place = places[0]
                if current_place is None:
                    current_place = place
                    start_day = day
                elif current_place != place:
                    # Flight from current_place to place
                    itinerary.append({"day_range": f"Day {start_day}-{day-1}", "place": current_place})
                    itinerary.append({"day_range": f"Day {day}", "place": current_place})
                    itinerary.append({"day_range": f"Day {day}", "place": place})
                    current_place = place
                    start_day = day
                # else continue the stay
            else:
                # Flight day: two places
                if current_place is None:
                    # Shouldn't happen per constraints
                    pass
                else:
                    # The current place is one of the two, the other is the new place.
                    other_place = [p for p in places if p != current_place][0]
                    itinerary.append({"day_range": f"Day {start_day}-{day}", "place": current_place})
                    itinerary.append({"day_range": f"Day {day}", "place": current_place})
                    itinerary.append({"day_range": f"Day {day}", "place": other_place})
                    current_place = other_place
                    start_day = day + 1
        # Add the last stay
        if current_place is not None:
            itinerary.append({"day_range": f"Day {start_day}-{days}", "place": current_place})
        
        # Clean up the itinerary by merging consecutive same-place entries
        cleaned_itinerary = []
        i = 0
        n = len(itinerary)
        while i < n:
            entry = itinerary[i]
            if i + 1 < n and itinerary[i+1]['place'] == entry['place']:
                # Merge consecutive entries for the same place.
                current_day_range = entry['day_range']
                next_day_range = itinerary[i+1]['day_range']
                # Parse day ranges.
                def parse_days(s):
                    if '-' in s:
                        start, end = s.replace('Day ', '').split('-')
                        return int(start), int(end)
                    else:
                        day = int(s.replace('Day ', ''))
                        return day, day
                start1, end1 = parse_days(current_day_range)
                start2, end2 = parse_days(next_day_range)
                new_start = min(start1, start2)
                new_end = max(end1, end2)
                merged_entry = {"day_range": f"Day {new_start}-{new_end}", "place": entry['place']}
                cleaned_itinerary.append(merged_entry)
                i += 2
            else:
                cleaned_itinerary.append(entry)
                i += 1
        
        # Further clean to handle flight days properly
        final_itinerary = []
        i = 0
        n = len(cleaned_itinerary)
        while i < n:
            entry = cleaned_itinerary[i]
            if i + 1 < n:
                next_entry = cleaned_itinerary[i+1]
                # Check if current entry's end day is the same as next entry's start day, and different places.
                current_day_range = entry['day_range']
                next_day_range = next_entry['day_range']
                current_start, current_end = parse_days(current_day_range)
                next_start, next_end = parse_days(next_day_range)
                if current_end == next_start and entry['place'] != next_entry['place']:
                    # Flight day.
                    final_itinerary.append({"day_range": f"Day {current_start}-{current_end}", "place": entry['place']})
                    final_itinerary.append({"day_range": f"Day {current_end}", "place": entry['place']})
                    final_itinerary.append({"day_range": f"Day {next_start}", "place": next_entry['place']})
                    # The next entry's remaining days will be handled in the next iteration.
                    if next_start == next_end:
                        i += 2
                    else:
                        new_next_entry = {"day_range": f"Day {next_start + 1}-{next_end}", "place": next_entry['place']}
                        cleaned_itinerary[i+1] = new_next_entry
                        i += 1
                else:
                    final_itinerary.append(entry)
                    i += 1
            else:
                final_itinerary.append(entry)
                i += 1
        
        return {"itinerary": final_itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
print(json.dumps(result, indent=2))