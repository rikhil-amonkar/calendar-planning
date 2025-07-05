import z3
from itertools import combinations

def solve_itinerary():
    # Cities and their required days
    cities = ["Berlin", "Split", "Bucharest", "Riga", "Lisbon", "Tallinn", "Lyon"]
    required_days = {
        "Berlin": 5,
        "Split": 3,
        "Bucharest": 3,
        "Riga": 5,
        "Lisbon": 3,
        "Tallinn": 4,
        "Lyon": 5
    }
    
    # Direct flights as tuples (from, to), bidirectional
    direct_flights = [
        ("Lisbon", "Bucharest"),
        ("Berlin", "Lisbon"),
        ("Bucharest", "Riga"),
        ("Berlin", "Riga"),
        ("Split", "Lyon"),
        ("Lisbon", "Riga"),
        ("Riga", "Tallinn"),
        ("Berlin", "Split"),
        ("Lyon", "Lisbon"),
        ("Berlin", "Tallinn"),
        ("Lyon", "Bucharest")
    ]
    
    # Make flights bidirectional
    flights = set()
    for a, b in direct_flights:
        flights.add((a, b))
        flights.add((b, a))
    
    days = 22
    
    # Create Z3 variables: city assigned to each day
    # day_place[d][c] is True if on day d+1, we are in city c
    day_place = [[z3.Bool(f"day_{d+1}_{c}") for c in cities] for d in range(days)]
    
    s = z3.Solver()
    
    # Constraint: Each day must be in exactly one city (except flight days, which are handled separately)
    for d in range(days):
        # At least one city per day
        s.add(z3.Or([day_place[d][i] for i in range(len(cities))]))
        # At most one city per day (no same-day flights for now; handled later)
        for i, j in combinations(range(len(cities)), 2):
            s.add(z3.Or(z3.Not(day_place[d][i]), z3.Not(day_place[d][j])))
    
    # Fixed constraints:
    # Berlin from day 1 to 5 (days 0..4 in zero-based)
    for d in range(5):
        s.add(day_place[d][cities.index("Berlin")])
    
    # Bucharest between day 13 and 15 (days 12..14 in zero-based)
    for d in range(12, 15):
        s.add(day_place[d][cities.index("Bucharest")])
    
    # Lyon between day 7 and 11 (days 6..10 in zero-based)
    for d in range(6, 11):
        s.add(day_place[d][cities.index("Lyon")])
    
    # Flight transitions: if day d is city A and day d+1 is city B, then (A,B) must be in flights
    for d in range(days - 1):
        for i in range(len(cities)):
            for j in range(len(cities)):
                if i != j:
                    # If day d is city i and day d+1 is city j, then (i,j) must be a flight
                    city_i = cities[i]
                    city_j = cities[j]
                    if (city_i, city_j) not in flights:
                        s.add(z3.Implies(day_place[d][i], z3.Not(day_place[d+1][j])))
    
    # Total days per city
    for c in range(len(cities)):
        city = cities[c]
        total = 0
        for d in range(days):
            total += z3.If(day_place[d][c], 1, 0)
        s.add(total == required_days[city])
    
    # Check and get model
    if s.check() == z3.sat:
        model = s.model()
        itinerary = []
        
        # Determine the stay ranges
        current_place = None
        start_day = 1
        for d in range(days):
            day_num = d + 1
            for c in range(len(cities)):
                if z3.is_true(model.eval(day_place[d][c])):
                    place = cities[c]
                    if place == current_place:
                        continue
                    else:
                        if current_place is not None:
                            # End previous stay
                            end_day = day_num - 1
                            if start_day == end_day:
                                itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
                            else:
                                itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": current_place})
                        # Start new stay
                        current_place = place
                        start_day = day_num
                        itinerary.append({"day_range": f"Day {day_num}", "place": place})
        # Add the last stay
        end_day = days
        if start_day == end_day:
            itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
        else:
            itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": current_place})
        
        # Now, handle flight days: when consecutive days are different, the day is both places
        # Reconstruct the day assignments
        day_assignments = []
        for d in range(days):
            for c in range(len(cities)):
                if z3.is_true(model.eval(day_place[d][c])):
                    day_assignments.append(cities[c])
                    break
        
        # Now, build the itinerary with flight days
        final_itinerary = []
        prev_place = None
        for day in range(1, days + 1):
            current_place = day_assignments[day - 1]
            if prev_place is not None and prev_place != current_place:
                # It's a flight day: add both places
                final_itinerary.append({"day_range": f"Day {day}", "place": prev_place})
                final_itinerary.append({"day_range": f"Day {day}", "place": current_place})
            else:
                final_itinerary.append({"day_range": f"Day {day}", "place": current_place})
            prev_place = current_place
        
        # Now, merge consecutive days for the same place into ranges
        optimized_itinerary = []
        i = 0
        n = len(final_itinerary)
        while i < n:
            current = final_itinerary[i]
            place = current["place"]
            start_day = int(current["day_range"].split("Day ")[1].split("-")[0])
            end_day = start_day
            j = i + 1
            while j < n:
                next_entry = final_itinerary[j]
                if next_entry["place"] == place and next_entry["day_range"] == f"Day {end_day + 1}":
                    end_day += 1
                    j += 1
                else:
                    break
            if start_day == end_day:
                optimized_itinerary.append({"day_range": f"Day {start_day}", "place": place})
            else:
                optimized_itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": place})
            i = j
        
        return {"itinerary": optimized_itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Execute and print the result
result = solve_itinerary()
print(result)