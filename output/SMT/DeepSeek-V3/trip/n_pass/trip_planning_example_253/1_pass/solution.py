from z3 import *
import json

def solve_itinerary():
    # Cities
    cities = ['Amsterdam', 'Vienna', 'Santorini', 'Lyon']
    direct_flights = {
        ('Vienna', 'Lyon'), ('Vienna', 'Santorini'), ('Vienna', 'Amsterdam'),
        ('Amsterdam', 'Santorini'), ('Lyon', 'Amsterdam')
    }
    # Make sure flights are bidirectional
    all_flights = set()
    for a, b in direct_flights:
        all_flights.add((a, b))
        all_flights.add((b, a))
    
    # Days are 1..14
    days = range(1, 15)
    n_days = 14
    
    # Create a solver
    s = Solver()
    
    # Variables: in_city[day][city] is true if the person is in that city on that day
    in_city = {}
    for day in days:
        in_city[day] = {}
        for city in cities:
            in_city[day][city] = Bool(f'in_{city}_day_{day}')
    
    # Constraint: each day, the person is in at least one city (but can be two on flight days)
    for day in days:
        # The person is in at least one city each day
        s.add(Or([in_city[day][city] for city in cities]))
    
    # Flight constraints: if in city A on day X and city B on day X+1, then there's a flight between A and B
    for day in range(1, n_days):
        for city1 in cities:
            for city2 in cities:
                if city1 != city2:
                    # If in city1 on day and city2 on day+1, then flight must exist
                    if (city1, city2) not in all_flights:
                        s.add(Not(And(in_city[day][city1], in_city[day+1][city2])))
    
    # Total days per city
    # Amsterdam: 3 days (including flight days)
    amsterdam_days = Sum([If(in_city[day]['Amsterdam'], 1, 0) for day in days])
    s.add(amsterdam_days == 3)
    
    # Vienna: 7 days
    vienna_days = Sum([If(in_city[day]['Vienna'], 1, 0) for day in days])
    s.add(vienna_days == 7)
    
    # Santorini: 4 days
    santorini_days = Sum([If(in_city[day]['Santorini'], 1, 0) for day in days])
    s.add(santorini_days == 4)
    
    # Lyon: 3 days
    lyon_days = Sum([If(in_city[day]['Lyon'], 1, 0) for day in days])
    s.add(lyon_days == 3)
    
    # Workshop in Amsterdam between day 9-11: at least one of days 9,10,11 must be in Amsterdam
    workshop_days = Or(in_city[9]['Amsterdam'], in_city[10]['Amsterdam'], in_city[11]['Amsterdam'])
    s.add(workshop_days)
    
    # Wedding in Lyon between day 7-9: at least one of days 7,8,9 must be in Lyon
    wedding_days = Or(in_city[7]['Lyon'], in_city[8]['Lyon'], in_city[9]['Lyon'])
    s.add(wedding_days)
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        # Extract the itinerary
        itinerary = []
        
        # Determine for each day which cities are visited
        day_to_cities = {}
        for day in days:
            day_cities = []
            for city in cities:
                if is_true(model.eval(in_city[day][city])):
                    day_cities.append(city)
            day_to_cities[day] = day_cities
        
        # Now, build the itinerary by grouping consecutive days in the same city(ies)
        current_places = day_to_cities[1]
        start_day = 1
        for day in range(2, n_days + 1):
            if day_to_cities[day] == current_places:
                continue
            else:
                # Add the previous block
                if len(current_places) == 1:
                    place = current_places[0]
                    if start_day == day - 1:
                        itinerary.append({"day_range": f"Day {start_day}", "place": place})
                    else:
                        itinerary.append({"day_range": f"Day {start_day}-{day - 1}", "place": place})
                else:
                    # Flight day: each city in current_places is present on the same day
                    # So, for each city in current_places, add a Day X entry
                    for place in current_places:
                        itinerary.append({"day_range": f"Day {start_day}", "place": place})
                current_places = day_to_cities[day]
                start_day = day
        # Add the last block
        if len(current_places) == 1:
            place = current_places[0]
            if start_day == n_days:
                itinerary.append({"day_range": f"Day {start_day}", "place": place})
            else:
                itinerary.append({"day_range": f"Day {start_day}-{n_days}", "place": place})
        else:
            for place in current_places:
                itinerary.append({"day_range": f"Day {start_day}", "place": place})
        
        # Now, handle overlapping flight days (days where two cities are visited)
        # We need to ensure that for flight days, both cities are listed separately for the same day
        # The current code should already handle this, but let's verify
        # Reconstruct the itinerary properly
        final_itinerary = []
        prev_day = None
        i = 0
        while i < len(itinerary):
            entry = itinerary[i]
            day_range = entry['day_range']
            if '-' in day_range:
                start, end = map(int, day_range.replace('Day ', '').split('-'))
                if start == end:
                    day = start
                    final_itinerary.append({"day_range": f"Day {day}", "place": entry['place']})
                else:
                    # Add the range
                    final_itinerary.append(entry)
            else:
                day = int(day_range.replace('Day ', ''))
                # Check if there are other entries with the same day
                same_day_entries = [entry]
                j = i + 1
                while j < len(itinerary):
                    next_entry = itinerary[j]
                    next_day_range = next_entry['day_range']
                    if '-' in next_day_range:
                        next_start, next_end = map(int, next_day_range.replace('Day ', '').split('-'))
                        if next_start == next_end and next_start == day:
                            same_day_entries.append(next_entry)
                            j += 1
                        else:
                            break
                    else:
                        next_day = int(next_day_range.replace('Day ', ''))
                        if next_day == day:
                            same_day_entries.append(next_entry)
                            j += 1
                        else:
                            break
                # Add all same_day entries
                for e in same_day_entries:
                    final_itinerary.append(e)
                i = j - 1
            i += 1
        
        # Now, merge consecutive entries for the same city
        optimized_itinerary = []
        i = 0
        n = len(final_itinerary)
        while i < n:
            current = final_itinerary[i]
            if i + 1 < n:
                next_entry = final_itinerary[i + 1]
                if current['place'] == next_entry['place']:
                    # Merge them
                    current_day = current['day_range']
                    next_day = next_entry['day_range']
                    if '-' in current_day:
                        start1, end1 = map(int, current_day.replace('Day ', '').split('-'))
                    else:
                        start1 = end1 = int(current_day.replace('Day ', ''))
                    if '-' in next_day:
                        start2, end2 = map(int, next_day.replace('Day ', '').split('-'))
                    else:
                        start2 = end2 = int(next_day.replace('Day ', ''))
                    new_start = min(start1, start2)
                    new_end = max(end1, end2)
                    if new_start == new_end:
                        new_day_range = f"Day {new_start}"
                    else:
                        new_day_range = f"Day {new_start}-{new_end}"
                    merged_entry = {"day_range": new_day_range, "place": current['place']}
                    optimized_itinerary.append(merged_entry)
                    i += 2  # skip the next entry as it's merged
                else:
                    optimized_itinerary.append(current)
                    i += 1
            else:
                optimized_itinerary.append(current)
                i += 1
        
        # Now, handle flight days where the same day appears in multiple entries
        # We need to ensure that flight days are listed separately for departure and arrival cities
        # So, for the optimized itinerary, if two entries have the same day, they should be separate
        final_output = []
        for entry in optimized_itinerary:
            day_range = entry['day_range']
            if '-' in day_range:
                start, end = map(int, day_range.replace('Day ', '').split('-'))
                if start == end:
                    final_output.append({"day_range": f"Day {start}", "place": entry['place']})
                else:
                    final_output.append(entry)
            else:
                day = int(day_range.replace('Day ', ''))
                final_output.append({"day_range": f"Day {day}", "place": entry['place']})
        
        # Now, check for any same-day entries and ensure they are separate
        # Group entries by day
        day_entries = {}
        for entry in final_output:
            day_range = entry['day_range']
            if '-' in day_range:
                start, end = map(int, day_range.replace('Day ', '').split('-'))
                for day in range(start, end + 1):
                    if day not in day_entries:
                        day_entries[day] = []
                    day_entries[day].append(entry['place'])
            else:
                day = int(day_range.replace('Day ', ''))
                if day not in day_entries:
                    day_entries[day] = []
                day_entries[day].append(entry['place'])
        
        # Now, build the final itinerary with separate entries for each city on flight days
        final_itinerary_json = []
        i = 0
        while i < len(final_output):
            entry = final_output[i]
            day_range = entry['day_range']
            if '-' in day_range:
                start, end = map(int, day_range.replace('Day ', '').split('-'))
                if start == end:
                    # Check if there are other entries for this day
                    day = start
                    places = day_entries.get(day, [])
                    if len(places) > 1:
                        # Add each place separately
                        for place in places:
                            final_itinerary_json.append({"day_range": f"Day {day}", "place": place})
                    else:
                        final_itinerary_json.append(entry)
                else:
                    final_itinerary_json.append(entry)
            else:
                day = int(day_range.replace('Day ', ''))
                places = day_entries.get(day, [])
                if len(places) > 1:
                    for place in places:
                        final_itinerary_json.append({"day_range": f"Day {day}", "place": place})
                else:
                    final_itinerary_json.append(entry)
            i += 1
        
        # Remove duplicates while preserving order
        seen = set()
        unique_itinerary = []
        for entry in final_itinerary_json:
            key = (entry['day_range'], entry['place'])
            if key not in seen:
                seen.add(key)
                unique_itinerary.append(entry)
        
        return {"itinerary": unique_itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Execute the function and print the result
result = solve_itinerary()
print(json.dumps(result, indent=2))